-- Analysis/BeneficialRounding.lean
--
-- Exact examples from Higham Chapter 1, Section 1.15.

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Prime.Basic
import LeanFpAnalysis.FP.Analysis.FloatingPointArithmetic
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra

namespace LeanFpAnalysis.FP

open Filter

open scoped BigOperators
open scoped Topology

/-!
# Rounding Errors Can Be Beneficial

This file records the exact real-arithmetic part of the power-method example in
Higham §1.15. The matrix is singular and the displayed starting vector is a
zero-eigenvalue eigenvector, so exact arithmetic produces the zero vector in one
power-method step. The file also records the terminating-binary storage
obstruction, the concrete IEEE-double entrywise storage first step, and the
exact first-step perturbation substrate. It does not claim the subsequent
MATLAB iteration trace.
-/

/-- A real number with a terminating binary expansion: `z / 2^n`. -/
def BinaryTerminating (x : ℝ) : Prop :=
  ∃ z : ℤ, ∃ n : ℕ, x = z / (2 : ℝ) ^ n

/-- Every entry of a displayed real matrix has a terminating binary expansion. -/
def MatrixEntriesBinaryTerminating {m n : Type*} (A : m → n → ℝ) : Prop :=
  ∀ i j, BinaryTerminating (A i j)

/-- Every entry of a displayed real matrix belongs exactly to a finite
floating-point format. -/
def MatrixEntriesFiniteSystem {m n : Type*}
    (fmt : FloatingPointFormat) (A : m → n → ℝ) : Prop :=
  ∀ i j, FloatingPointFormat.finiteSystem fmt (A i j)

/-- No power of two is divisible by five. -/
theorem five_not_dvd_two_pow_nat (n : ℕ) : ¬ (5 : ℕ) ∣ 2 ^ n := by
  intro h
  have hp : Nat.Prime 5 := by decide
  have h52 : (5 : ℕ) ∣ 2 := hp.dvd_of_dvd_pow h
  norm_num at h52

/-- No power of two is divisible by three. -/
theorem three_not_dvd_two_pow_nat (n : ℕ) : ¬ (3 : ℕ) ∣ 2 ^ n := by
  intro h
  have hp : Nat.Prime 3 := by decide
  have h32 : (3 : ℕ) ∣ 2 := hp.dvd_of_dvd_pow h
  norm_num at h32

/-- No power of two is divisible by seven. -/
theorem seven_not_dvd_two_pow_nat (n : ℕ) : ¬ (7 : ℕ) ∣ 2 ^ n := by
  intro h
  have hp : Nat.Prime 7 := by decide
  have h72 : (7 : ℕ) ∣ 2 := hp.dvd_of_dvd_pow h
  norm_num at h72

/-- The source entry `1/5` is not a terminating binary fraction. -/
theorem one_fifth_not_binaryTerminating :
    ¬ BinaryTerminating (1 / 5 : ℝ) := by
  rintro ⟨z, n, h⟩
  have hpow_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hmul : (2 : ℝ) ^ n = (5 : ℝ) * z := by
    field_simp [hpow_ne] at h
    linarith
  have hmul_int : (2 : ℤ) ^ n = 5 * z := by
    exact_mod_cast hmul
  have hdiv_int : (5 : ℤ) ∣ (2 : ℤ) ^ n := by
    exact ⟨z, hmul_int⟩
  have hdiv_nat : (5 : ℕ) ∣ 2 ^ n := by
    exact_mod_cast hdiv_int
  exact five_not_dvd_two_pow_nat n hdiv_nat

/-- The source input `2/3` is not a terminating binary fraction. -/
theorem two_thirds_not_binaryTerminating :
    ¬ BinaryTerminating (2 / 3 : ℝ) := by
  rintro ⟨z, n, h⟩
  have hpow_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hmul : (2 : ℝ) * (2 : ℝ) ^ n = (3 : ℝ) * z := by
    field_simp [hpow_ne] at h
    linarith
  have hmul_int : (2 : ℤ) * (2 : ℤ) ^ n = 3 * z := by
    exact_mod_cast hmul
  have hpow_int : (2 : ℤ) ^ (n + 1) = 3 * z := by
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul_int
  have hdiv_int : (3 : ℤ) ∣ (2 : ℤ) ^ (n + 1) := by
    exact ⟨z, hpow_int⟩
  have hdiv_nat : (3 : ℕ) ∣ 2 ^ (n + 1) := by
    exact_mod_cast hdiv_int
  exact three_not_dvd_two_pow_nat (n + 1) hdiv_nat

/-- The source input `1/7` is not a terminating binary fraction. -/
theorem one_seventh_not_binaryTerminating :
    ¬ BinaryTerminating (1 / 7 : ℝ) := by
  rintro ⟨z, n, h⟩
  have hpow_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hmul : (2 : ℝ) ^ n = (7 : ℝ) * z := by
    field_simp [hpow_ne] at h
    linarith
  have hmul_int : (2 : ℤ) ^ n = 7 * z := by
    exact_mod_cast hmul
  have hdiv_int : (7 : ℤ) ∣ (2 : ℤ) ^ n := by
    exact ⟨z, hmul_int⟩
  have hdiv_nat : (7 : ℕ) ∣ 2 ^ n := by
    exact_mod_cast hdiv_int
  exact seven_not_dvd_two_pow_nat n hdiv_nat

/-- For every positive power of ten, `1/10^m` is not a terminating binary
fraction.  This records the §1.11 observation that `1/n` has a nonterminating
binary expansion when `n` is a power of ten. -/
theorem one_div_ten_pow_succ_not_binaryTerminating (k : ℕ) :
    ¬ BinaryTerminating (1 / (10 : ℝ) ^ (k + 1)) := by
  rintro ⟨z, n, h⟩
  have hpow2_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hpow10_ne : (10 : ℝ) ^ (k + 1) ≠ 0 := by positivity
  have hmul : (2 : ℝ) ^ n = (10 : ℝ) ^ (k + 1) * z := by
    field_simp [hpow2_ne, hpow10_ne] at h
    linarith
  have hmul_int : (2 : ℤ) ^ n = (10 : ℤ) ^ (k + 1) * z := by
    exact_mod_cast hmul
  have h10dvd : (10 : ℤ) ^ (k + 1) ∣ (2 : ℤ) ^ n := by
    exact ⟨z, hmul_int⟩
  have h5dvd10 : (5 : ℤ) ∣ (10 : ℤ) := by norm_num
  have hk1_ne : k + 1 ≠ 0 := by exact Nat.succ_ne_zero k
  have h5dvd10pow : (5 : ℤ) ∣ (10 : ℤ) ^ (k + 1) :=
    dvd_pow h5dvd10 hk1_ne
  have hdiv_int : (5 : ℤ) ∣ (2 : ℤ) ^ n :=
    dvd_trans h5dvd10pow h10dvd
  have hdiv_nat : (5 : ℕ) ∣ 2 ^ n := by
    exact_mod_cast hdiv_int
  exact five_not_dvd_two_pow_nat n hdiv_nat

/-- Every normalized IEEE-double finite value is a terminating binary fraction.
The fixed denominator `2^1074` is the least-positive-subnormal denominator. -/
theorem ieeeDoubleFormat_normalizedSystem_binaryTerminating
    {x : ℝ}
    (hx : FloatingPointFormat.normalizedSystem
      FloatingPointFormat.ieeeDoubleFormat x) :
    BinaryTerminating x := by
  rcases hx with ⟨negative, m, e, _hm, he, hx⟩
  have he' : -1021 ≤ e ∧ e ≤ 1024 := by
    simpa [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange] using he
  have hk_nonneg : 0 ≤ e + 1021 := by omega
  let k : ℕ := Int.toNat (e + 1021)
  let zAbs : ℤ := (m : ℤ) * (2 : ℤ) ^ k
  refine ⟨if negative then -zAbs else zAbs, 1074, ?_⟩
  rw [hx]
  subst k
  subst zAbs
  have htoNat : (((e + 1021).toNat : ℕ) : ℤ) = e + 1021 :=
    Int.toNat_of_nonneg hk_nonneg
  have hpow :
      (2 : ℝ) ^ (e - 53) =
        (2 : ℝ) ^ ((e + 1021).toNat : ℕ) * ((2 : ℝ) ^ 1074)⁻¹ := by
    have hsplit : e - 53 = (e + 1021) - (1074 : ℤ) := by ring
    rw [hsplit]
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have hnum :
        (2 : ℝ) ^ (e + 1021) =
          (2 : ℝ) ^ ((e + 1021).toNat : ℕ) := by
      rw [← htoNat]
      exact zpow_natCast (2 : ℝ) ((e + 1021).toNat)
    have hden :
        (2 : ℝ) ^ (1074 : ℤ) = (2 : ℝ) ^ (1074 : ℕ) := by
      simpa using (zpow_natCast (2 : ℝ) (1074 : ℕ))
    rw [hnum, hden]
    rw [div_eq_mul_inv]
  have hzAbs_cast :
      (((m : ℤ) * (2 : ℤ) ^ (e + 1021).toNat : ℤ) : ℝ) =
        (m : ℝ) * (2 : ℝ) ^ ((e + 1021).toNat : ℕ) := by
    norm_num [Int.cast_pow]
  cases negative
  · simp [FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.ieeeDoubleFormat, hpow,
      div_eq_mul_inv, hzAbs_cast, mul_assoc]
  · simp [FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.ieeeDoubleFormat, hpow,
      div_eq_mul_inv, hzAbs_cast, mul_assoc]

/-- Every normalized IEEE-single finite value is a terminating binary fraction.
The fixed denominator `2^149` is the least-positive-subnormal denominator. -/
theorem ieeeSingleFormat_normalizedSystem_binaryTerminating
    {x : ℝ}
    (hx : FloatingPointFormat.normalizedSystem
      FloatingPointFormat.ieeeSingleFormat x) :
    BinaryTerminating x := by
  rcases hx with ⟨negative, m, e, _hm, he, hx⟩
  have he' : -125 ≤ e ∧ e ≤ 128 := by
    simpa [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange] using he
  have hk_nonneg : 0 ≤ e + 125 := by omega
  let k : ℕ := Int.toNat (e + 125)
  let zAbs : ℤ := (m : ℤ) * (2 : ℤ) ^ k
  refine ⟨if negative then -zAbs else zAbs, 149, ?_⟩
  rw [hx]
  subst k
  subst zAbs
  have htoNat : (((e + 125).toNat : ℕ) : ℤ) = e + 125 :=
    Int.toNat_of_nonneg hk_nonneg
  have hpow :
      (2 : ℝ) ^ (e - 24) =
        (2 : ℝ) ^ ((e + 125).toNat : ℕ) * ((2 : ℝ) ^ 149)⁻¹ := by
    have hsplit : e - 24 = (e + 125) - (149 : ℤ) := by ring
    rw [hsplit]
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have hnum :
        (2 : ℝ) ^ (e + 125) =
          (2 : ℝ) ^ ((e + 125).toNat : ℕ) := by
      rw [← htoNat]
      exact zpow_natCast (2 : ℝ) ((e + 125).toNat)
    have hden :
        (2 : ℝ) ^ (149 : ℤ) = (2 : ℝ) ^ (149 : ℕ) := by
      simpa using (zpow_natCast (2 : ℝ) (149 : ℕ))
    rw [hnum, hden]
    rw [div_eq_mul_inv]
  have hzAbs_cast :
      (((m : ℤ) * (2 : ℤ) ^ (e + 125).toNat : ℤ) : ℝ) =
        (m : ℝ) * (2 : ℝ) ^ ((e + 125).toNat : ℕ) := by
    norm_num [Int.cast_pow]
  cases negative
  · simp [FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.ieeeSingleFormat, hpow,
      div_eq_mul_inv, hzAbs_cast, mul_assoc]
  · simp [FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.ieeeSingleFormat, hpow,
      div_eq_mul_inv, hzAbs_cast, mul_assoc]

/-- Every subnormal IEEE-double finite value is a terminating binary fraction,
again with denominator `2^1074`. -/
theorem ieeeDoubleFormat_subnormalSystem_binaryTerminating
    {x : ℝ}
    (hx : FloatingPointFormat.subnormalSystem
      FloatingPointFormat.ieeeDoubleFormat x) :
    BinaryTerminating x := by
  rcases hx with ⟨negative, m, _hm, hx⟩
  let zAbs : ℤ := m
  refine ⟨if negative then -zAbs else zAbs, 1074, ?_⟩
  rw [hx]
  subst zAbs
  have hpow :
      (2 : ℝ) ^ (-1074 : ℤ) = ((2 : ℝ) ^ (1074 : ℕ))⁻¹ := by
    rw [zpow_neg]
    rw [show (1074 : ℤ) = ((1074 : ℕ) : ℤ) by norm_num]
    rw [zpow_natCast]
  cases negative
  · simp [FloatingPointFormat.subnormalValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.ieeeDoubleFormat, hpow,
      div_eq_mul_inv]
  · simp [FloatingPointFormat.subnormalValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.ieeeDoubleFormat, hpow,
      div_eq_mul_inv]

/-- Every subnormal IEEE-single finite value is a terminating binary fraction,
again with denominator `2^149`. -/
theorem ieeeSingleFormat_subnormalSystem_binaryTerminating
    {x : ℝ}
    (hx : FloatingPointFormat.subnormalSystem
      FloatingPointFormat.ieeeSingleFormat x) :
    BinaryTerminating x := by
  rcases hx with ⟨negative, m, _hm, hx⟩
  let zAbs : ℤ := m
  refine ⟨if negative then -zAbs else zAbs, 149, ?_⟩
  rw [hx]
  subst zAbs
  have hpow :
      (2 : ℝ) ^ (-149 : ℤ) = ((2 : ℝ) ^ (149 : ℕ))⁻¹ := by
    rw [zpow_neg]
    rw [show (149 : ℤ) = ((149 : ℕ) : ℤ) by norm_num]
    rw [zpow_natCast]
  cases negative
  · simp [FloatingPointFormat.subnormalValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.ieeeSingleFormat, hpow,
      div_eq_mul_inv]
  · simp [FloatingPointFormat.subnormalValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.ieeeSingleFormat, hpow,
      div_eq_mul_inv]

/-- Every finite IEEE-double value is a terminating binary fraction. -/
theorem ieeeDoubleFormat_finiteSystem_binaryTerminating
    {x : ℝ}
    (hx : FloatingPointFormat.finiteSystem
      FloatingPointFormat.ieeeDoubleFormat x) :
    BinaryTerminating x := by
  rcases hx with hx0 | hnorm | hsub
  · refine ⟨0, 0, ?_⟩
    simp [hx0]
  · exact ieeeDoubleFormat_normalizedSystem_binaryTerminating hnorm
  · exact ieeeDoubleFormat_subnormalSystem_binaryTerminating hsub

/-- Every finite IEEE-single value is a terminating binary fraction. -/
theorem ieeeSingleFormat_finiteSystem_binaryTerminating
    {x : ℝ}
    (hx : FloatingPointFormat.finiteSystem
      FloatingPointFormat.ieeeSingleFormat x) :
    BinaryTerminating x := by
  rcases hx with hx0 | hnorm | hsub
  · refine ⟨0, 0, ?_⟩
    simp [hx0]
  · exact ieeeSingleFormat_normalizedSystem_binaryTerminating hnorm
  · exact ieeeSingleFormat_subnormalSystem_binaryTerminating hsub

/-- The source entry `1/5` is not exactly an IEEE-double finite value. -/
theorem one_fifth_not_ieeeDoubleFiniteSystem :
    ¬ FloatingPointFormat.finiteSystem
      FloatingPointFormat.ieeeDoubleFormat (1 / 5 : ℝ) := by
  intro h
  exact one_fifth_not_binaryTerminating
    (ieeeDoubleFormat_finiteSystem_binaryTerminating h)

/-- The source input `2/3` is not exactly an IEEE-single finite value. -/
theorem two_thirds_not_ieeeSingleFiniteSystem :
    ¬ FloatingPointFormat.finiteSystem
      FloatingPointFormat.ieeeSingleFormat (2 / 3 : ℝ) := by
  intro h
  exact two_thirds_not_binaryTerminating
    (ieeeSingleFormat_finiteSystem_binaryTerminating h)

/-- The source input `1/7` is not exactly an IEEE-single finite value. -/
theorem one_seventh_not_ieeeSingleFiniteSystem :
    ¬ FloatingPointFormat.finiteSystem
      FloatingPointFormat.ieeeSingleFormat (1 / 7 : ℝ) := by
  intro h
  exact one_seventh_not_binaryTerminating
    (ieeeSingleFormat_finiteSystem_binaryTerminating h)

/-- The source input `2/3` is not exactly an IEEE-double finite value. -/
theorem two_thirds_not_ieeeDoubleFiniteSystem :
    ¬ FloatingPointFormat.finiteSystem
      FloatingPointFormat.ieeeDoubleFormat (2 / 3 : ℝ) := by
  intro h
  exact two_thirds_not_binaryTerminating
    (ieeeDoubleFormat_finiteSystem_binaryTerminating h)

/-- The source input `1/7` is not exactly an IEEE-double finite value. -/
theorem one_seventh_not_ieeeDoubleFiniteSystem :
    ¬ FloatingPointFormat.finiteSystem
      FloatingPointFormat.ieeeDoubleFormat (1 / 7 : ℝ) := by
  intro h
  exact one_seventh_not_binaryTerminating
    (ieeeDoubleFormat_finiteSystem_binaryTerminating h)

private theorem ieeeDoubleFormat_minNormalMagnitude_le_one_fifth :
    FloatingPointFormat.ieeeDoubleFormat.minNormalMagnitude ≤ (1 / 5 : ℝ) := by
  norm_num [FloatingPointFormat.ieeeDoubleFormat,
    FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
    zpow_neg]
  have hden : (5 : ℝ) ≤ (2 : ℝ) ^ 1022 := by
    have hsmall : (5 : ℝ) ≤ (2 : ℝ) ^ 3 := by norm_num
    have hmono : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ 1022 :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (3 : ℕ) ≤ 1022)
    exact hsmall.trans hmono
  simpa [one_div] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5) hden

private theorem ieeeDoubleFormat_minNormalMagnitude_le_one_tenth :
    FloatingPointFormat.ieeeDoubleFormat.minNormalMagnitude ≤ (1 / 10 : ℝ) := by
  norm_num [FloatingPointFormat.ieeeDoubleFormat,
    FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
    zpow_neg]
  have hden : (10 : ℝ) ≤ (2 : ℝ) ^ 1022 := by
    have hsmall : (10 : ℝ) ≤ (2 : ℝ) ^ 4 := by norm_num
    have hmono : (2 : ℝ) ^ 4 ≤ (2 : ℝ) ^ 1022 :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (4 : ℕ) ≤ 1022)
    exact hsmall.trans hmono
  simpa [one_div] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 10) hden

private theorem ieeeDoubleFormat_one_le_maxFiniteMagnitude :
    (1 : ℝ) ≤ FloatingPointFormat.ieeeDoubleFormat.maxFiniteMagnitude := by
  norm_num [FloatingPointFormat.ieeeDoubleFormat,
    FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
    zpow_neg]
  have hpow_ge_two : (2 : ℝ) ≤ (2 : ℝ) ^ 1024 := by
    have hmono : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ 1024 :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (1 : ℕ) ≤ 1024)
    simpa using hmono
  have hfirst : (1 : ℝ) ≤ (2 : ℝ) ^ 1024 * (1 / 2 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hpow_ge_two
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    norm_num at h
    exact h
  have hhalf : (1 / 2 : ℝ) ≤
      (9007199254740991 : ℝ) / 9007199254740992 := by norm_num
  exact hfirst.trans
    (mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ (2 : ℝ) ^ 1024))

/-- The source fraction `1/5` lies in the IEEE-double normal range. -/
theorem ieeeDoubleFormat_one_fifth_finiteNormalRange :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange (1 / 5 : ℝ) := by
  rw [FloatingPointFormat.finiteNormalRange,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 5)]
  constructor
  · exact ieeeDoubleFormat_minNormalMagnitude_le_one_fifth
  · calc
      (1 / 5 : ℝ) ≤ 1 := by norm_num
      _ ≤ FloatingPointFormat.ieeeDoubleFormat.maxFiniteMagnitude :=
        ieeeDoubleFormat_one_le_maxFiniteMagnitude

/-- The source fraction `1/10` lies in the IEEE-double normal range. -/
theorem ieeeDoubleFormat_one_tenth_finiteNormalRange :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange (1 / 10 : ℝ) := by
  rw [FloatingPointFormat.finiteNormalRange,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 10)]
  constructor
  · exact ieeeDoubleFormat_minNormalMagnitude_le_one_tenth
  · calc
      (1 / 10 : ℝ) ≤ 1 := by norm_num
      _ ≤ FloatingPointFormat.ieeeDoubleFormat.maxFiniteMagnitude :=
        ieeeDoubleFormat_one_le_maxFiniteMagnitude

/-- The source fraction `2/5` lies in the IEEE-double normal range. -/
theorem ieeeDoubleFormat_two_fifths_finiteNormalRange :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange (2 / 5 : ℝ) := by
  rw [FloatingPointFormat.finiteNormalRange,
    abs_of_pos (by norm_num : (0 : ℝ) < 2 / 5)]
  constructor
  · exact ieeeDoubleFormat_minNormalMagnitude_le_one_fifth.trans
      (by norm_num : (1 / 5 : ℝ) ≤ 2 / 5)
  · calc
      (2 / 5 : ℝ) ≤ 1 := by norm_num
      _ ≤ FloatingPointFormat.ieeeDoubleFormat.maxFiniteMagnitude :=
        ieeeDoubleFormat_one_le_maxFiniteMagnitude

/-- The source fraction `3/10` lies in the IEEE-double normal range. -/
theorem ieeeDoubleFormat_three_tenths_finiteNormalRange :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange (3 / 10 : ℝ) := by
  rw [FloatingPointFormat.finiteNormalRange,
    abs_of_pos (by norm_num : (0 : ℝ) < 3 / 10)]
  constructor
  · exact ieeeDoubleFormat_minNormalMagnitude_le_one_tenth.trans
      (by norm_num : (1 / 10 : ℝ) ≤ 3 / 10)
  · calc
      (3 / 10 : ℝ) ≤ 1 := by norm_num
      _ ≤ FloatingPointFormat.ieeeDoubleFormat.maxFiniteMagnitude :=
        ieeeDoubleFormat_one_le_maxFiniteMagnitude

/-- The source fraction `3/5` lies in the IEEE-double normal range. -/
theorem ieeeDoubleFormat_three_fifths_finiteNormalRange :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange (3 / 5 : ℝ) := by
  rw [FloatingPointFormat.finiteNormalRange,
    abs_of_pos (by norm_num : (0 : ℝ) < 3 / 5)]
  constructor
  · exact ieeeDoubleFormat_minNormalMagnitude_le_one_fifth.trans
      (by norm_num : (1 / 5 : ℝ) ≤ 3 / 5)
  · calc
      (3 / 5 : ℝ) ≤ 1 := by norm_num
      _ ≤ FloatingPointFormat.ieeeDoubleFormat.maxFiniteMagnitude :=
        ieeeDoubleFormat_one_le_maxFiniteMagnitude

/-- The source fraction `7/10` lies in the IEEE-double normal range. -/
theorem ieeeDoubleFormat_seven_tenths_finiteNormalRange :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange (7 / 10 : ℝ) := by
  rw [FloatingPointFormat.finiteNormalRange,
    abs_of_pos (by norm_num : (0 : ℝ) < 7 / 10)]
  constructor
  · exact ieeeDoubleFormat_minNormalMagnitude_le_one_tenth.trans
      (by norm_num : (1 / 10 : ℝ) ≤ 7 / 10)
  · calc
      (7 / 10 : ℝ) ≤ 1 := by norm_num
      _ ≤ FloatingPointFormat.ieeeDoubleFormat.maxFiniteMagnitude :=
        ieeeDoubleFormat_one_le_maxFiniteMagnitude

/-- IEEE-double round-to-even sends `1/5` to its upper adjacent normal value. -/
theorem ieeeDoubleFormat_one_fifth_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (1 / 5 : ℝ) =
      (7205759403792794 : ℝ) * (2 : ℝ) ^ (-55 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false 7205759403792793 (-2 : ℤ)
  let b : ℝ := fmt.normalizedValue false 7205759403792794 (-2 : ℤ)
  let x : ℝ := (1 / 5 : ℝ)
  have hm : fmt.normalizedMantissa 7205759403792793 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (7205759403792793 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 7205759403792793, (-2 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (7205759403792793 : ℝ) * (2 : ℝ) ^ (-55 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hb_value :
      b = (7205759403792794 : ℝ) * (2 : ℝ) ^ (-55 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      ieeeDoubleFormat_one_fifth_finiteNormalRange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [x, fmt, hb_value] using hround

/-- IEEE-double round-to-even sends `1/10` to its upper adjacent normal value. -/
theorem ieeeDoubleFormat_one_tenth_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (1 / 10 : ℝ) =
      (7205759403792794 : ℝ) * (2 : ℝ) ^ (-56 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false 7205759403792793 (-3 : ℤ)
  let b : ℝ := fmt.normalizedValue false 7205759403792794 (-3 : ℤ)
  let x : ℝ := (1 / 10 : ℝ)
  have hm : fmt.normalizedMantissa 7205759403792793 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (7205759403792793 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 7205759403792793, (-3 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (7205759403792793 : ℝ) * (2 : ℝ) ^ (-56 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hb_value :
      b = (7205759403792794 : ℝ) * (2 : ℝ) ^ (-56 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      ieeeDoubleFormat_one_tenth_finiteNormalRange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [x, fmt, hb_value] using hround

/-- IEEE-double round-to-even sends `2/5` to its upper adjacent normal value. -/
theorem ieeeDoubleFormat_two_fifths_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (2 / 5 : ℝ) =
      (7205759403792794 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false 7205759403792793 (-1 : ℤ)
  let b : ℝ := fmt.normalizedValue false 7205759403792794 (-1 : ℤ)
  let x : ℝ := (2 / 5 : ℝ)
  have hm : fmt.normalizedMantissa 7205759403792793 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (7205759403792793 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 7205759403792793, (-1 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (7205759403792793 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hb_value :
      b = (7205759403792794 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      ieeeDoubleFormat_two_fifths_finiteNormalRange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [x, fmt, hb_value] using hround

/-- IEEE-double round-to-even sends `3/10` to its lower adjacent normal value. -/
theorem ieeeDoubleFormat_three_tenths_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (3 / 10 : ℝ) =
      (5404319552844595 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false 5404319552844595 (-1 : ℤ)
  let b : ℝ := fmt.normalizedValue false 5404319552844596 (-1 : ℤ)
  let x : ℝ := (3 / 10 : ℝ)
  have hm : fmt.normalizedMantissa 5404319552844595 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (5404319552844595 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 5404319552844595, (-1 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (5404319552844595 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hb_value :
      b = (5404319552844596 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      ieeeDoubleFormat_three_tenths_finiteNormalRange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [x, fmt, ha_value] using hround

/-- IEEE-double round-to-even sends `3/5` to its lower adjacent normal value. -/
theorem ieeeDoubleFormat_three_fifths_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (3 / 5 : ℝ) =
      (5404319552844595 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false 5404319552844595 (0 : ℤ)
  let b : ℝ := fmt.normalizedValue false 5404319552844596 (0 : ℤ)
  let x : ℝ := (3 / 5 : ℝ)
  have hm : fmt.normalizedMantissa 5404319552844595 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (5404319552844595 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 5404319552844595, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (5404319552844595 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hb_value :
      b = (5404319552844596 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      ieeeDoubleFormat_three_fifths_finiteNormalRange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [x, fmt, ha_value] using hround

/-- IEEE-double round-to-even sends `7/10` to its lower adjacent normal value. -/
theorem ieeeDoubleFormat_seven_tenths_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (7 / 10 : ℝ) =
      (6305039478318694 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false 6305039478318694 (0 : ℤ)
  let b : ℝ := fmt.normalizedValue false 6305039478318695 (0 : ℤ)
  let x : ℝ := (7 / 10 : ℝ)
  have hm : fmt.normalizedMantissa 6305039478318694 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (6305039478318694 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 6305039478318694, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (6305039478318694 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hb_value :
      b = (6305039478318695 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      ieeeDoubleFormat_seven_tenths_finiteNormalRange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [x, fmt, ha_value] using hround

/-- IEEE-double round-to-even is symmetric on the source fraction `1/10`. -/
theorem ieeeDoubleFormat_neg_one_tenth_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (-1 / 10 : ℝ) =
      -((7205759403792794 : ℝ) * (2 : ℝ) ^ (-56 : ℤ)) := by
  have hneg :=
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven_neg_of_finiteNormalRange
      (by norm_num [FloatingPointFormat.evenMantissa,
        FloatingPointFormat.ieeeDoubleFormat])
      (by norm_num [FloatingPointFormat.ieeeDoubleFormat])
      ieeeDoubleFormat_one_tenth_finiteNormalRange
  have hround := ieeeDoubleFormat_one_tenth_rounds_to
  rw [show (-1 / 10 : ℝ) = -(1 / 10 : ℝ) by norm_num]
  rw [hneg, hround]

/-- IEEE-double round-to-even is symmetric on the source fraction `2/5`. -/
theorem ieeeDoubleFormat_neg_two_fifths_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (-2 / 5 : ℝ) =
      -((7205759403792794 : ℝ) * (2 : ℝ) ^ (-54 : ℤ)) := by
  have hneg :=
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven_neg_of_finiteNormalRange
      (by norm_num [FloatingPointFormat.evenMantissa,
        FloatingPointFormat.ieeeDoubleFormat])
      (by norm_num [FloatingPointFormat.ieeeDoubleFormat])
      ieeeDoubleFormat_two_fifths_finiteNormalRange
  have hround := ieeeDoubleFormat_two_fifths_rounds_to
  rw [show (-2 / 5 : ℝ) = -(2 / 5 : ℝ) by norm_num]
  rw [hneg, hround]

/-- IEEE-double round-to-even is symmetric on the source fraction `3/10`. -/
theorem ieeeDoubleFormat_neg_three_tenths_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (-3 / 10 : ℝ) =
      -((5404319552844595 : ℝ) * (2 : ℝ) ^ (-54 : ℤ)) := by
  have hneg :=
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven_neg_of_finiteNormalRange
      (by norm_num [FloatingPointFormat.evenMantissa,
        FloatingPointFormat.ieeeDoubleFormat])
      (by norm_num [FloatingPointFormat.ieeeDoubleFormat])
      ieeeDoubleFormat_three_tenths_finiteNormalRange
  have hround := ieeeDoubleFormat_three_tenths_rounds_to
  rw [show (-3 / 10 : ℝ) = -(3 / 10 : ℝ) by norm_num]
  rw [hneg, hround]

/-- The source fraction `1/2` is an exact IEEE-double finite value. -/
theorem ieeeDoubleFormat_one_half_finiteSystem :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem (1 / 2 : ℝ) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hm : fmt.normalizedMantissa 4503599627370496 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (0 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  have hval :
      fmt.normalizedValue false 4503599627370496 (0 : ℤ) = (1 / 2 : ℝ) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hfin : fmt.finiteSystem
      (fmt.normalizedValue false 4503599627370496 (0 : ℤ)) :=
    Or.inr (Or.inl ⟨false, 4503599627370496, (0 : ℤ), hm, he, rfl⟩)
  simpa [fmt, hval] using hfin

/-- IEEE-double round-to-even fixes the exactly representable source fraction
`1/2`. -/
theorem ieeeDoubleFormat_one_half_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (1 / 2 : ℝ) =
      (1 / 2 : ℝ) := by
  exact
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven_eq_self_of_finiteSystem
      ieeeDoubleFormat_one_half_finiteSystem

/-- The tiny dyadic `2^-54` is an exact IEEE-double finite value. -/
theorem ieeeDoubleFormat_two_pow_neg54_finiteSystem :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem
      ((1 : ℝ) / (2 : ℝ) ^ 54) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hm : fmt.normalizedMantissa 4503599627370496 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (-53 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  have hval :
      fmt.normalizedValue false 4503599627370496 (-53 : ℤ) =
        ((1 : ℝ) / (2 : ℝ) ^ 54) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hfin : fmt.finiteSystem
      (fmt.normalizedValue false 4503599627370496 (-53 : ℤ)) :=
    Or.inr (Or.inl ⟨false, 4503599627370496, (-53 : ℤ), hm, he, rfl⟩)
  simpa [fmt, hval] using hfin

/-- The tiny dyadic `2^-55` is an exact IEEE-double finite value. -/
theorem ieeeDoubleFormat_two_pow_neg55_finiteSystem :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem
      ((1 : ℝ) / (2 : ℝ) ^ 55) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hm : fmt.normalizedMantissa 4503599627370496 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (-54 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  have hval :
      fmt.normalizedValue false 4503599627370496 (-54 : ℤ) =
        ((1 : ℝ) / (2 : ℝ) ^ 55) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hfin : fmt.finiteSystem
      (fmt.normalizedValue false 4503599627370496 (-54 : ℤ)) :=
    Or.inr (Or.inl ⟨false, 4503599627370496, (-54 : ℤ), hm, he, rfl⟩)
  simpa [fmt, hval] using hfin

/-- At the lower edge of the binade containing `1/2`, the value
`1/2 + 2^-55` is still closer to `1/2` than to the next IEEE-double value. -/
theorem ieeeDoubleFormat_half_plus_two_pow_neg55_rounds_to_half :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven
        ((1 : ℝ) / 2 + (2 : ℝ) ^ (-55 : ℤ)) =
      (1 / 2 : ℝ) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false fmt.minNormalMantissa 0
  let b : ℝ := fmt.normalizedValue false (fmt.minNormalMantissa + 1) 0
  let x : ℝ := (1 : ℝ) / 2 + (2 : ℝ) ^ (-55 : ℤ)
  have hm : fmt.normalizedMantissa fmt.minNormalMantissa :=
    fmt.minNormalMantissa_normalized
  have hmnext : fmt.normalizedMantissa (fmt.minNormalMantissa + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, fmt.minNormalMantissa, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (1 / 2 : ℝ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.minNormalMantissa,
      zpow_neg]
  have hb_value : b = (1 / 2 : ℝ) + (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.minNormalMantissa,
      zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by norm_num [x, zpow_neg]
    rw [abs_of_nonneg hxnonneg]
    constructor
    · exact le_trans ieeeDoubleFormat_minNormalMagnitude_le_one_tenth
        (by norm_num [x, zpow_neg] : (1 / 10 : ℝ) ≤ x)
    · exact le_trans (by norm_num [x, zpow_neg] : x ≤ (1 : ℝ))
        ieeeDoubleFormat_one_le_maxFiniteMagnitude
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [x, fmt, ha_value] using hround

/-- Signed companion of
`ieeeDoubleFormat_half_plus_two_pow_neg55_rounds_to_half`. -/
theorem ieeeDoubleFormat_neg_half_plus_two_pow_neg55_rounds_to_neg_half :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven
        (-((1 : ℝ) / 2 + (2 : ℝ) ^ (-55 : ℤ))) =
      -(1 / 2 : ℝ) := by
  rw [FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven_neg]
  · rw [ieeeDoubleFormat_half_plus_two_pow_neg55_rounds_to_half]
  · norm_num [FloatingPointFormat.evenMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat]

/-- IEEE-double round-to-even is symmetric on the source fraction `3/5`. -/
theorem ieeeDoubleFormat_neg_three_fifths_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (-3 / 5 : ℝ) =
      -((5404319552844595 : ℝ) * (2 : ℝ) ^ (-53 : ℤ)) := by
  have hneg :=
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven_neg_of_finiteNormalRange
      (by norm_num [FloatingPointFormat.evenMantissa,
        FloatingPointFormat.ieeeDoubleFormat])
      (by norm_num [FloatingPointFormat.ieeeDoubleFormat])
      ieeeDoubleFormat_three_fifths_finiteNormalRange
  have hround := ieeeDoubleFormat_three_fifths_rounds_to
  rw [show (-3 / 5 : ℝ) = -(3 / 5 : ℝ) by norm_num]
  rw [hneg, hround]

/-- One unnormalized power-method step, `x := A*x`. -/
noncomputable def powerMethodStep (n : ℕ) (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  matMulVec n A x

/-- `k` unnormalized power-method steps, starting from `x`. -/
noncomputable def powerMethodIterate (n : ℕ) (A : Fin n → Fin n → ℝ) :
    ℕ → (Fin n → ℝ) → (Fin n → ℝ)
  | 0, x => x
  | k + 1, x => powerMethodStep n A (powerMethodIterate n A k x)

/-- A nonzero right-eigenvector/eigenvalue relation for legacy square matrices. -/
def IsRightEigenpair (n : ℕ) (A : Fin n → Fin n → ℝ)
    (lambda : ℝ) (x : Fin n → ℝ) : Prop :=
  (∃ i : Fin n, x i ≠ 0) ∧
    ∀ i : Fin n, matMulVec n A x i = lambda * x i

/-- The shifted matrix `A - mu I` used in inverse iteration. -/
noncomputable def inverseIterationShiftedMatrix (n : ℕ)
    (A : Fin n → Fin n → ℝ) (mu : ℝ) : Fin n → Fin n → ℝ :=
  fun i j => A i j - mu * idMatrix n i j

/-- The shifted linear solve `(A - mu I) y = x` used to apply the shifted
inverse without explicitly forming it. -/
def SolvesInverseIterationShiftedSystem (n : ℕ)
    (A : Fin n → Fin n → ℝ) (mu : ℝ)
    (x y : Fin n → ℝ) : Prop :=
  matMulVec n (inverseIterationShiftedMatrix n A mu) y = x

/-- Multiplying by the shifted matrix subtracts `mu*x` from `A*x`. -/
theorem inverseIterationShiftedMatrix_mulVec (n : ℕ)
    (A : Fin n → Fin n → ℝ) (mu : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    matMulVec n (inverseIterationShiftedMatrix n A mu) x i =
      matMulVec n A x i - mu * x i := by
  unfold matMulVec inverseIterationShiftedMatrix
  have hscale :
      (∑ j : Fin n, (mu * idMatrix n i j) * x j) = mu * x i := by
    calc
      (∑ j : Fin n, (mu * idMatrix n i j) * x j)
          = mu * (∑ j : Fin n, idMatrix n i j * x j) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = mu * x i := by
          have hid := congrFun (idMatrix_mulVec n x) i
          simp [hid]
  calc
    (∑ j : Fin n, (A i j - mu * idMatrix n i j) * x j)
        = (∑ j : Fin n, A i j * x j) -
            (∑ j : Fin n, (mu * idMatrix n i j) * x j) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = (∑ j : Fin n, A i j * x j) - mu * x i := by
          rw [hscale]

/-- If `x` is an eigenvector of `A`, then `A - mu I` maps it to
`(lambda - mu) x`. -/
theorem inverseIteration_shiftedMatrix_mul_eigenvector
    {n : ℕ} {A : Fin n → Fin n → ℝ} {lambda mu : ℝ}
    {x : Fin n → ℝ} (hx : IsRightEigenpair n A lambda x) (i : Fin n) :
    matMulVec n (inverseIterationShiftedMatrix n A mu) x i =
      (lambda - mu) * x i := by
  rw [inverseIterationShiftedMatrix_mulVec]
  rw [hx.2 i]
  ring

/-- On an eigenvector direction, the inverse-iteration shifted solve has the
exact solution `(lambda - mu)^{-1} x`. -/
theorem inverseIteration_shiftedSystem_solution_on_eigenvector
    {n : ℕ} {A : Fin n → Fin n → ℝ} {lambda mu : ℝ}
    {x : Fin n → ℝ} (hx : IsRightEigenpair n A lambda x)
    (hshift : lambda - mu ≠ 0) :
    SolvesInverseIterationShiftedSystem n A mu x
      (fun i => (lambda - mu)⁻¹ * x i) := by
  unfold SolvesInverseIterationShiftedSystem
  ext i
  calc
    matMulVec n (inverseIterationShiftedMatrix n A mu)
        (fun i => (lambda - mu)⁻¹ * x i) i
        = (lambda - mu)⁻¹ *
            matMulVec n (inverseIterationShiftedMatrix n A mu) x i := by
            unfold matMulVec
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = (lambda - mu)⁻¹ * ((lambda - mu) * x i) := by
          rw [inverseIteration_shiftedMatrix_mul_eigenvector hx i]
    _ = x i := by
          rw [← mul_assoc, inv_mul_cancel₀ hshift, one_mul]

/-- If `B` is a left inverse for `A - mu I`, then applying the shifted inverse
to an eigenvector scales that eigenvector by `(lambda - mu)^{-1}`. -/
theorem inverseIteration_shiftedInverse_mul_eigenvector_of_leftInverse
    {n : ℕ} {A B : Fin n → Fin n → ℝ} {lambda mu : ℝ}
    {x : Fin n → ℝ} (hx : IsRightEigenpair n A lambda x)
    (hshift : lambda - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B) :
    matMulVec n B x = fun i => (lambda - mu)⁻¹ * x i := by
  let y : Fin n → ℝ := fun i => (lambda - mu)⁻¹ * x i
  have hsolve :
      matMulVec n (inverseIterationShiftedMatrix n A mu) y = x := by
    simpa [y] using inverseIteration_shiftedSystem_solution_on_eigenvector hx hshift
  have hmat :
      matMul n B (inverseIterationShiftedMatrix n A mu) = idMatrix n := by
    ext i j
    exact hB i j
  ext i
  calc
    matMulVec n B x i
        = matMulVec n B
            (matMulVec n (inverseIterationShiftedMatrix n A mu) y) i := by
            rw [hsolve]
    _ = matMulVec n
          (matMul n B (inverseIterationShiftedMatrix n A mu)) y i := by
          rw [matMulVec_matMul]
    _ = y i := by
          rw [hmat, matMulVec_id]
    _ = (lambda - mu)⁻¹ * x i := rfl

/-- The scalar amplification in inverse iteration is the reciprocal of the
distance from the shift to the eigenvalue. -/
theorem inverseIteration_shiftedInverse_amplification_abs_eq
    (lambda mu : ℝ) :
    |(lambda - mu)⁻¹| = (|lambda - mu|)⁻¹ := by
  rw [abs_inv]

/-- A shift closer to an eigenvalue gives a larger exact inverse-iteration
scalar amplification. -/
theorem inverseIteration_shiftedInverse_amplification_strict_of_abs_shift_lt
    {lambda muClose muFar : ℝ}
    (hclose_pos : 0 < |lambda - muClose|)
    (hclose_far : |lambda - muClose| < |lambda - muFar|) :
    |(lambda - muFar)⁻¹| < |(lambda - muClose)⁻¹| := by
  rw [abs_inv, abs_inv]
  simpa [one_div] using
    one_div_lt_one_div_of_lt hclose_pos hclose_far

/-- Matrix-vector multiplication commutes with scalar multiplication in the
vector argument. -/
theorem matMulVec_smul_right (n : ℕ) (A : Fin n → Fin n → ℝ)
    (c : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    matMulVec n A (fun j => c * x j) i = c * matMulVec n A x i := by
  unfold matMulVec
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Matrix-vector multiplication distributes over a finite sum in the vector
argument. -/
theorem matMulVec_fin_sum_right {m n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin m → Fin n → ℝ) (i : Fin n) :
    matMulVec n A (fun j => ∑ a : Fin m, x a j) i =
      ∑ a : Fin m, matMulVec n A (x a) i := by
  unfold matMulVec
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Finite-sum Euclidean triangle inequality over an arbitrary finite set. -/
theorem vecNorm2_finset_sum_le {α : Type*} [DecidableEq α] {n : ℕ}
    (s : Finset α) (x : α → Fin n → ℝ) :
    vecNorm2 (fun i => Finset.sum s (fun a => x a i)) ≤
      Finset.sum s (fun a => vecNorm2 (x a)) := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · simp [vecNorm2_zero]
  · intro a s has ih
    calc
      vecNorm2 (fun i => Finset.sum (insert a s) (fun b => x b i))
          = vecNorm2 (fun i => x a i + Finset.sum s (fun b => x b i)) := by
              congr 1
              ext i
              simp [Finset.sum_insert has]
      _ ≤ vecNorm2 (x a) +
            vecNorm2 (fun i => Finset.sum s (fun b => x b i)) :=
          vecNorm2_add_le (x a) (fun i => Finset.sum s (fun b => x b i))
      _ ≤ vecNorm2 (x a) + Finset.sum s (fun b => vecNorm2 (x b)) := by
          linarith [ih]
      _ = Finset.sum (insert a s) (fun b => vecNorm2 (x b)) := by
          rw [Finset.sum_insert has]

/-- Finite-family Euclidean triangle inequality for `Fin m`-indexed vectors. -/
theorem vecNorm2_fin_sum_le {m n : ℕ}
    (x : Fin m → Fin n → ℝ) :
    vecNorm2 (fun i => ∑ a : Fin m, x a i) ≤
      ∑ a : Fin m, vecNorm2 (x a) := by
  simpa using
    vecNorm2_finset_sum_le (s := (Finset.univ : Finset (Fin m))) x

/-- If a starting vector is a sum of two right-eigenvector components, then
`k` unnormalized power-method steps scale each component by the corresponding
`k`th eigenvalue power.  This is the algebraic substrate for the Chapter 1
statement that a nonzero dominant component is amplified relative to smaller
components. -/
theorem powerMethodIterate_two_eigencomponents
    {n : ℕ} {A : Fin n → Fin n → ℝ}
    {lambdaDominant lambdaOther coeffDominant coeffOther : ℝ}
    {vDominant vOther : Fin n → ℝ}
    (hDominant : IsRightEigenpair n A lambdaDominant vDominant)
    (hOther : IsRightEigenpair n A lambdaOther vOther) (k : ℕ) :
    powerMethodIterate n A k
        (fun i => coeffDominant * vDominant i + coeffOther * vOther i) =
      fun i =>
        coeffDominant * lambdaDominant ^ k * vDominant i +
          coeffOther * lambdaOther ^ k * vOther i := by
  induction k with
  | zero =>
      ext i
      simp [powerMethodIterate]
  | succ k ih =>
      ext i
      calc
        powerMethodIterate n A (k + 1)
            (fun i => coeffDominant * vDominant i + coeffOther * vOther i) i
            = powerMethodStep n A
                (fun i =>
                  coeffDominant * lambdaDominant ^ k * vDominant i +
                    coeffOther * lambdaOther ^ k * vOther i) i := by
                simp [powerMethodIterate, ih]
        _ = coeffDominant * lambdaDominant ^ (k + 1) * vDominant i +
              coeffOther * lambdaOther ^ (k + 1) * vOther i := by
              unfold powerMethodStep
              rw [congrFun
                (matMulVec_add_right n A
                  (fun i => coeffDominant * lambdaDominant ^ k * vDominant i)
                  (fun i => coeffOther * lambdaOther ^ k * vOther i)) i]
              rw [matMulVec_smul_right, matMulVec_smul_right]
              rw [hDominant.2 i, hOther.2 i]
              ring

/-- Finite-tail version of the power-method eigencomponent identity.  If the
starting vector is a dominant right-eigenvector component plus any finite sum
of other right-eigenvector components, then `k` unnormalized power-method steps
scale each component by the corresponding `k`th eigenvalue power. -/
theorem powerMethodIterate_dominant_plus_finite_tail
    {n m : ℕ} {A : Fin n → Fin n → ℝ}
    {lambdaDominant coeffDominant : ℝ}
    {lambdaTail coeffTail : Fin m → ℝ}
    {vDominant : Fin n → ℝ} {vTail : Fin m → Fin n → ℝ}
    (hDominant : IsRightEigenpair n A lambdaDominant vDominant)
    (hTail : ∀ a : Fin m, IsRightEigenpair n A (lambdaTail a) (vTail a))
    (k : ℕ) :
    powerMethodIterate n A k
        (fun i => coeffDominant * vDominant i +
          ∑ a : Fin m, coeffTail a * vTail a i) =
      fun i =>
        coeffDominant * lambdaDominant ^ k * vDominant i +
          ∑ a : Fin m, coeffTail a * lambdaTail a ^ k * vTail a i := by
  induction k with
  | zero =>
      ext i
      simp [powerMethodIterate]
  | succ k ih =>
      ext i
      calc
        powerMethodIterate n A (k + 1)
            (fun i => coeffDominant * vDominant i +
              ∑ a : Fin m, coeffTail a * vTail a i) i
            = powerMethodStep n A
                (fun i =>
                  coeffDominant * lambdaDominant ^ k * vDominant i +
                    ∑ a : Fin m,
                      coeffTail a * lambdaTail a ^ k * vTail a i) i := by
                simp [powerMethodIterate, ih]
        _ = coeffDominant * lambdaDominant ^ (k + 1) * vDominant i +
              ∑ a : Fin m,
                coeffTail a * lambdaTail a ^ (k + 1) * vTail a i := by
              unfold powerMethodStep
              have htail :
                  matMulVec n A
                      (fun i =>
                        ∑ a : Fin m,
                          coeffTail a * lambdaTail a ^ k * vTail a i) i =
                    ∑ a : Fin m,
                      coeffTail a * lambdaTail a ^ (k + 1) * vTail a i := by
                rw [matMulVec_fin_sum_right]
                apply Finset.sum_congr rfl
                intro a _
                rw [matMulVec_smul_right]
                rw [(hTail a).2 i]
                ring
              rw [congrFun
                (matMulVec_add_right n A
                  (fun i => coeffDominant * lambdaDominant ^ k * vDominant i)
                  (fun i =>
                    ∑ a : Fin m,
                      coeffTail a * lambdaTail a ^ k * vTail a i)) i]
              rw [matMulVec_smul_right]
              rw [hDominant.2 i, htail]
              ring

/-- Exact ratio formula for the scalar coefficients in the two-component power
method model: the non-dominant-to-dominant component ratio is the initial
coefficient ratio times the spectral ratio to the `k`th power. -/
theorem powerMethod_component_abs_ratio_eq_initial_mul_spectral_ratio
    {lambdaDominant lambdaOther coeffDominant coeffOther : ℝ} (k : ℕ)
    (hCoeff : coeffDominant ≠ 0) (hLambda : lambdaDominant ≠ 0) :
    |coeffOther * lambdaOther ^ k| /
        |coeffDominant * lambdaDominant ^ k| =
      (|coeffOther| / |coeffDominant|) *
        (|lambdaOther| / |lambdaDominant|) ^ k := by
  have hCoeffAbs : |coeffDominant| ≠ 0 :=
    ne_of_gt (abs_pos.mpr hCoeff)
  have hLambdaAbs : |lambdaDominant| ≠ 0 :=
    ne_of_gt (abs_pos.mpr hLambda)
  rw [abs_mul, abs_mul, abs_pow, abs_pow, div_pow]
  field_simp [hCoeffAbs, hLambdaAbs, pow_ne_zero k hLambdaAbs]

/-- Linear-rate ratio bound for the two-component power-method model.  If the
spectral ratio is at most `q`, then the smaller component is bounded by the
initial component ratio times `q^k`. -/
theorem powerMethod_component_abs_ratio_le_geometric_of_spectral_ratio_le
    {lambdaDominant lambdaOther coeffDominant coeffOther q : ℝ} (k : ℕ)
    (hCoeff : coeffDominant ≠ 0) (hLambda : lambdaDominant ≠ 0)
    (hRatio : |lambdaOther| / |lambdaDominant| ≤ q) :
    |coeffOther * lambdaOther ^ k| /
        |coeffDominant * lambdaDominant ^ k| ≤
      (|coeffOther| / |coeffDominant|) * q ^ k := by
  rw [powerMethod_component_abs_ratio_eq_initial_mul_spectral_ratio
    (k := k) hCoeff hLambda]
  have hSpectralNonneg : 0 ≤ |lambdaOther| / |lambdaDominant| :=
    div_nonneg (abs_nonneg _) (abs_nonneg _)
  have hpow :
      (|lambdaOther| / |lambdaDominant|) ^ k ≤ q ^ k :=
    pow_le_pow_left₀ hSpectralNonneg hRatio k
  exact mul_le_mul_of_nonneg_left hpow
    (div_nonneg (abs_nonneg _) (abs_nonneg _))

/-- Convergence-rate form of the same two-component power-method model: if the
spectral ratio is strictly below one, the non-dominant-to-dominant coefficient
ratio tends to zero. -/
theorem powerMethod_component_abs_ratio_tendsto_zero_of_spectral_ratio_lt_one
    {lambdaDominant lambdaOther coeffDominant coeffOther : ℝ}
    (hCoeff : coeffDominant ≠ 0) (hLambda : lambdaDominant ≠ 0)
    (hRatioNonneg : 0 ≤ |lambdaOther| / |lambdaDominant|)
    (hRatioLtOne : |lambdaOther| / |lambdaDominant| < 1) :
    Tendsto
      (fun k : ℕ =>
        |coeffOther * lambdaOther ^ k| /
          |coeffDominant * lambdaDominant ^ k|)
      atTop (𝓝 0) := by
  have hpow :
      Tendsto
        (fun k : ℕ => (|lambdaOther| / |lambdaDominant|) ^ k)
        atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hRatioNonneg hRatioLtOne
  have hfun :
      (fun k : ℕ =>
        |coeffOther * lambdaOther ^ k| /
          |coeffDominant * lambdaDominant ^ k|) =
        fun k : ℕ =>
          (|coeffOther| / |coeffDominant|) *
            (|lambdaOther| / |lambdaDominant|) ^ k := by
    funext k
    exact powerMethod_component_abs_ratio_eq_initial_mul_spectral_ratio
      (k := k) hCoeff hLambda
  rw [hfun]
  simpa using hpow.const_mul (|coeffOther| / |coeffDominant|)

/-- Aggregate geometric bound for a finite non-dominant tail in the
power-method model.  If every tail spectral ratio is at most `q`, then the sum
of tail coefficient magnitudes, normalized by the dominant coefficient
magnitude, is bounded by the initial finite-tail ratio times `q^k`. -/
theorem powerMethod_finite_tail_abs_sum_ratio_le_geometric_of_spectral_ratio_le
    {m : ℕ} {lambdaDominant coeffDominant q : ℝ}
    {lambdaTail coeffTail : Fin m → ℝ} (k : ℕ)
    (hCoeff : coeffDominant ≠ 0) (hLambda : lambdaDominant ≠ 0)
    (hRatio : ∀ a : Fin m, |lambdaTail a| / |lambdaDominant| ≤ q) :
    (∑ a : Fin m, |coeffTail a * lambdaTail a ^ k|) /
        |coeffDominant * lambdaDominant ^ k| ≤
      ((∑ a : Fin m, |coeffTail a|) / |coeffDominant|) * q ^ k := by
  rw [Finset.sum_div]
  calc
    (∑ a : Fin m,
        |coeffTail a * lambdaTail a ^ k| /
          |coeffDominant * lambdaDominant ^ k|)
        ≤ ∑ a : Fin m, (|coeffTail a| / |coeffDominant|) * q ^ k := by
            apply Finset.sum_le_sum
            intro a _
            exact
              powerMethod_component_abs_ratio_le_geometric_of_spectral_ratio_le
                (k := k) (coeffOther := coeffTail a)
                (lambdaOther := lambdaTail a) hCoeff hLambda (hRatio a)
    _ = ((∑ a : Fin m, |coeffTail a|) / |coeffDominant|) * q ^ k := by
          rw [← Finset.sum_mul]
          congr 1
          rw [Finset.sum_div]

/-- The geometric upper bound used for a finite non-dominant power-method tail
tends to zero whenever the common spectral-ratio bound is strictly below one. -/
theorem powerMethod_finite_tail_geometric_bound_tendsto_zero
    {m : ℕ} {coeffDominant q : ℝ} {coeffTail : Fin m → ℝ}
    (hqNonneg : 0 ≤ q) (hqLtOne : q < 1) :
    Tendsto
      (fun k : ℕ =>
        ((∑ a : Fin m, |coeffTail a|) / |coeffDominant|) * q ^ k)
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun k : ℕ => q ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hqNonneg hqLtOne
  simpa using
    hpow.const_mul ((∑ a : Fin m, |coeffTail a|) / |coeffDominant|)

/-- Convergence-rate form for the finite-tail power-method model: under a
common spectral-ratio bound `q < 1`, the normalized aggregate non-dominant tail
tends to zero. -/
theorem powerMethod_finite_tail_abs_sum_ratio_tendsto_zero_of_geometric_bound
    {m : ℕ} {lambdaDominant coeffDominant q : ℝ}
    {lambdaTail coeffTail : Fin m → ℝ}
    (hCoeff : coeffDominant ≠ 0) (hLambda : lambdaDominant ≠ 0)
    (hRatio : ∀ a : Fin m, |lambdaTail a| / |lambdaDominant| ≤ q)
    (hqNonneg : 0 ≤ q) (hqLtOne : q < 1) :
    Tendsto
      (fun k : ℕ =>
        (∑ a : Fin m, |coeffTail a * lambdaTail a ^ k|) /
          |coeffDominant * lambdaDominant ^ k|)
      atTop (𝓝 0) := by
  have hUpper :
      ∀ k : ℕ,
        (∑ a : Fin m, |coeffTail a * lambdaTail a ^ k|) /
            |coeffDominant * lambdaDominant ^ k| ≤
          ((∑ a : Fin m, |coeffTail a|) / |coeffDominant|) * q ^ k :=
    fun k =>
      powerMethod_finite_tail_abs_sum_ratio_le_geometric_of_spectral_ratio_le
        (k := k) hCoeff hLambda hRatio
  have hLower :
      ∀ k : ℕ,
        0 ≤
          (∑ a : Fin m, |coeffTail a * lambdaTail a ^ k|) /
            |coeffDominant * lambdaDominant ^ k| :=
    fun _ =>
      div_nonneg
        (Finset.sum_nonneg fun a _ => abs_nonneg _)
        (abs_nonneg _)
  have hBoundTend :
      Tendsto
        (fun k : ℕ =>
          ((∑ a : Fin m, |coeffTail a|) / |coeffDominant|) * q ^ k)
        atTop (𝓝 0) :=
    powerMethod_finite_tail_geometric_bound_tendsto_zero
      (m := m) (coeffDominant := coeffDominant)
      (coeffTail := coeffTail) hqNonneg hqLtOne
  exact squeeze_zero hLower hUpper hBoundTend

/-- Norm-level finite-tail power-method bound.  The Euclidean norm of the
finite non-dominant tail, normalized by the dominant scalar magnitude, is
bounded by the initial weighted tail norm ratio times `q^k`. -/
theorem powerMethod_finite_tail_vecNorm2_ratio_le_geometric_of_spectral_ratio_le
    {n m : ℕ} {lambdaDominant coeffDominant q : ℝ}
    {lambdaTail coeffTail : Fin m → ℝ}
    {vTail : Fin m → Fin n → ℝ} (k : ℕ)
    (hCoeff : coeffDominant ≠ 0) (hLambda : lambdaDominant ≠ 0)
    (hRatio : ∀ a : Fin m, |lambdaTail a| / |lambdaDominant| ≤ q) :
    vecNorm2
        (fun i =>
          ∑ a : Fin m, coeffTail a * lambdaTail a ^ k * vTail a i) /
        |coeffDominant * lambdaDominant ^ k| ≤
      ((∑ a : Fin m, |coeffTail a| * vecNorm2 (vTail a)) /
          |coeffDominant|) * q ^ k := by
  have hnorm :
      vecNorm2
          (fun i =>
            ∑ a : Fin m, coeffTail a * lambdaTail a ^ k * vTail a i) ≤
        ∑ a : Fin m,
          vecNorm2
            (fun i => coeffTail a * lambdaTail a ^ k * vTail a i) :=
    vecNorm2_fin_sum_le
      (fun a i => coeffTail a * lambdaTail a ^ k * vTail a i)
  have hden_nonneg :
      0 ≤ |coeffDominant * lambdaDominant ^ k| := abs_nonneg _
  calc
    vecNorm2
        (fun i =>
          ∑ a : Fin m, coeffTail a * lambdaTail a ^ k * vTail a i) /
        |coeffDominant * lambdaDominant ^ k|
        ≤ (∑ a : Fin m,
            vecNorm2
              (fun i => coeffTail a * lambdaTail a ^ k * vTail a i)) /
          |coeffDominant * lambdaDominant ^ k| :=
            div_le_div_of_nonneg_right hnorm hden_nonneg
    _ = (∑ a : Fin m,
            |coeffTail a * lambdaTail a ^ k| * vecNorm2 (vTail a)) /
          |coeffDominant * lambdaDominant ^ k| := by
          congr 1
          apply Finset.sum_congr rfl
          intro a _
          rw [vecNorm2_smul]
    _ = ∑ a : Fin m,
          (|coeffTail a * lambdaTail a ^ k| /
              |coeffDominant * lambdaDominant ^ k|) *
            vecNorm2 (vTail a) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ ≤ ∑ a : Fin m,
          ((|coeffTail a| / |coeffDominant|) * q ^ k) *
            vecNorm2 (vTail a) := by
          apply Finset.sum_le_sum
          intro a _
          exact mul_le_mul_of_nonneg_right
            (powerMethod_component_abs_ratio_le_geometric_of_spectral_ratio_le
              (k := k) (coeffOther := coeffTail a)
              (lambdaOther := lambdaTail a) hCoeff hLambda (hRatio a))
            (vecNorm2_nonneg (vTail a))
    _ = ∑ a : Fin m,
          ((|coeffTail a| * vecNorm2 (vTail a)) /
              |coeffDominant|) * q ^ k := by
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = ((∑ a : Fin m, |coeffTail a| * vecNorm2 (vTail a)) /
          |coeffDominant|) * q ^ k := by
          rw [← Finset.sum_mul]
          congr 1
          rw [Finset.sum_div]

/-- Norm-level convergence form for a finite non-dominant tail in the
power-method model. -/
theorem powerMethod_finite_tail_vecNorm2_ratio_tendsto_zero_of_geometric_bound
    {n m : ℕ} {lambdaDominant coeffDominant q : ℝ}
    {lambdaTail coeffTail : Fin m → ℝ}
    {vTail : Fin m → Fin n → ℝ}
    (hCoeff : coeffDominant ≠ 0) (hLambda : lambdaDominant ≠ 0)
    (hRatio : ∀ a : Fin m, |lambdaTail a| / |lambdaDominant| ≤ q)
    (hqNonneg : 0 ≤ q) (hqLtOne : q < 1) :
    Tendsto
      (fun k : ℕ =>
        vecNorm2
            (fun i =>
              ∑ a : Fin m, coeffTail a * lambdaTail a ^ k * vTail a i) /
          |coeffDominant * lambdaDominant ^ k|)
      atTop (𝓝 0) := by
  have hLower :
      ∀ k : ℕ,
        0 ≤
          vecNorm2
              (fun i =>
                ∑ a : Fin m, coeffTail a * lambdaTail a ^ k * vTail a i) /
            |coeffDominant * lambdaDominant ^ k| :=
    fun _ => div_nonneg (vecNorm2_nonneg _) (abs_nonneg _)
  have hUpper :
      ∀ k : ℕ,
        vecNorm2
            (fun i =>
              ∑ a : Fin m, coeffTail a * lambdaTail a ^ k * vTail a i) /
            |coeffDominant * lambdaDominant ^ k| ≤
          ((∑ a : Fin m, |coeffTail a| * vecNorm2 (vTail a)) /
              |coeffDominant|) * q ^ k :=
    fun k =>
      powerMethod_finite_tail_vecNorm2_ratio_le_geometric_of_spectral_ratio_le
        (k := k) hCoeff hLambda hRatio
  have hpow : Tendsto (fun k : ℕ => q ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hqNonneg hqLtOne
  have hBoundTend :
      Tendsto
        (fun k : ℕ =>
          ((∑ a : Fin m, |coeffTail a| * vecNorm2 (vTail a)) /
              |coeffDominant|) * q ^ k)
        atTop (𝓝 0) := by
    simpa using
      hpow.const_mul
        ((∑ a : Fin m, |coeffTail a| * vecNorm2 (vTail a)) /
          |coeffDominant|)
  exact squeeze_zero hLower hUpper hBoundTend

/-- Direct finite-tail power-method residual bound: after subtracting the
dominant component from the actual `k`th unnormalized iterate, the normalized
Euclidean residual is bounded by the weighted finite-tail ratio times `q^k`. -/
theorem powerMethodIterate_dominant_scaled_residual_ratio_le_geometric_of_finite_tail
    {n m : ℕ} {A : Fin n → Fin n → ℝ}
    {lambdaDominant coeffDominant q : ℝ}
    {lambdaTail coeffTail : Fin m → ℝ}
    {vDominant : Fin n → ℝ} {vTail : Fin m → Fin n → ℝ}
    (hDominant : IsRightEigenpair n A lambdaDominant vDominant)
    (hTail : ∀ a : Fin m, IsRightEigenpair n A (lambdaTail a) (vTail a))
    (hCoeff : coeffDominant ≠ 0) (hLambda : lambdaDominant ≠ 0)
    (hRatio : ∀ a : Fin m, |lambdaTail a| / |lambdaDominant| ≤ q)
    (k : ℕ) :
    vecNorm2
        (fun i =>
          powerMethodIterate n A k
              (fun i => coeffDominant * vDominant i +
                ∑ a : Fin m, coeffTail a * vTail a i) i -
            coeffDominant * lambdaDominant ^ k * vDominant i) /
        |coeffDominant * lambdaDominant ^ k| ≤
      ((∑ a : Fin m, |coeffTail a| * vecNorm2 (vTail a)) /
          |coeffDominant|) * q ^ k := by
  have hres :
      vecNorm2
          (fun i =>
            powerMethodIterate n A k
                (fun i => coeffDominant * vDominant i +
                  ∑ a : Fin m, coeffTail a * vTail a i) i -
              coeffDominant * lambdaDominant ^ k * vDominant i) =
        vecNorm2
          (fun i =>
            ∑ a : Fin m, coeffTail a * lambdaTail a ^ k * vTail a i) := by
    congr 1
    ext i
    rw [congrFun
      (powerMethodIterate_dominant_plus_finite_tail
        hDominant hTail k) i]
    ring
  rw [hres]
  exact
    powerMethod_finite_tail_vecNorm2_ratio_le_geometric_of_spectral_ratio_le
      (k := k) hCoeff hLambda hRatio

/-- Direct convergence form of the finite-tail power-method bridge.  Under a
common spectral-ratio bound `0 <= q < 1`, the actual unnormalized iterate,
after subtracting the dominant component and scaling by the dominant scalar
magnitude, has Euclidean norm tending to zero. -/
theorem powerMethodIterate_dominant_scaled_residual_tendsto_zero_of_finite_tail
    {n m : ℕ} {A : Fin n → Fin n → ℝ}
    {lambdaDominant coeffDominant q : ℝ}
    {lambdaTail coeffTail : Fin m → ℝ}
    {vDominant : Fin n → ℝ} {vTail : Fin m → Fin n → ℝ}
    (hDominant : IsRightEigenpair n A lambdaDominant vDominant)
    (hTail : ∀ a : Fin m, IsRightEigenpair n A (lambdaTail a) (vTail a))
    (hCoeff : coeffDominant ≠ 0) (hLambda : lambdaDominant ≠ 0)
    (hRatio : ∀ a : Fin m, |lambdaTail a| / |lambdaDominant| ≤ q)
    (hqNonneg : 0 ≤ q) (hqLtOne : q < 1) :
    Tendsto
      (fun k : ℕ =>
        vecNorm2
            (fun i =>
              powerMethodIterate n A k
                  (fun i => coeffDominant * vDominant i +
                    ∑ a : Fin m, coeffTail a * vTail a i) i -
                coeffDominant * lambdaDominant ^ k * vDominant i) /
          |coeffDominant * lambdaDominant ^ k|)
      atTop (𝓝 0) := by
  have hfun :
      (fun k : ℕ =>
        vecNorm2
            (fun i =>
              powerMethodIterate n A k
                  (fun i => coeffDominant * vDominant i +
                    ∑ a : Fin m, coeffTail a * vTail a i) i -
                coeffDominant * lambdaDominant ^ k * vDominant i) /
          |coeffDominant * lambdaDominant ^ k|) =
        fun k : ℕ =>
          vecNorm2
              (fun i =>
                ∑ a : Fin m, coeffTail a * lambdaTail a ^ k * vTail a i) /
            |coeffDominant * lambdaDominant ^ k| := by
    funext k
    congr 1
    congr 1
    ext i
    rw [congrFun
      (powerMethodIterate_dominant_plus_finite_tail
        hDominant hTail k) i]
    ring
  rw [hfun]
  exact
    powerMethod_finite_tail_vecNorm2_ratio_tendsto_zero_of_geometric_bound
      hCoeff hLambda hRatio hqNonneg hqLtOne

/-- A reusable certificate that a starting vector has a nonzero dominant
eigencomponent plus a finite non-dominant tail with a common spectral-ratio
bound.  This is the exact handoff needed before the generic finite-tail
power-method convergence theorem can be applied to a concrete stored matrix. -/
structure PowerMethodDominantFiniteTailCertificate
    (n m : ℕ) (A : Fin n → Fin n → ℝ) (x0 : Fin n → ℝ) where
  lambdaDominant : ℝ
  coeffDominant : ℝ
  q : ℝ
  lambdaTail : Fin m → ℝ
  coeffTail : Fin m → ℝ
  vDominant : Fin n → ℝ
  vTail : Fin m → Fin n → ℝ
  start_decomposition :
    x0 = fun i => coeffDominant * vDominant i +
      ∑ a : Fin m, coeffTail a * vTail a i
  dominant_eigenpair : IsRightEigenpair n A lambdaDominant vDominant
  tail_eigenpairs :
    ∀ a : Fin m, IsRightEigenpair n A (lambdaTail a) (vTail a)
  coeffDominant_ne_zero : coeffDominant ≠ 0
  lambdaDominant_ne_zero : lambdaDominant ≠ 0
  tail_spectral_ratio_le :
    ∀ a : Fin m, |lambdaTail a| / |lambdaDominant| ≤ q
  q_nonneg : 0 ≤ q
  q_lt_one : q < 1

/-- A dominant finite-tail certificate immediately gives the scaled
power-method residual convergence theorem for the certified starting vector. -/
theorem PowerMethodDominantFiniteTailCertificate.scaled_residual_tendsto_zero
    {n m : ℕ} {A : Fin n → Fin n → ℝ} {x0 : Fin n → ℝ}
    (cert : PowerMethodDominantFiniteTailCertificate n m A x0) :
    Tendsto
      (fun k : ℕ =>
        vecNorm2
            (fun i =>
              powerMethodIterate n A k x0 i -
                cert.coeffDominant * cert.lambdaDominant ^ k *
                  cert.vDominant i) /
          |cert.coeffDominant * cert.lambdaDominant ^ k|)
      atTop (𝓝 0) := by
  simpa [cert.start_decomposition] using
    powerMethodIterate_dominant_scaled_residual_tendsto_zero_of_finite_tail
      cert.dominant_eigenpair cert.tail_eigenpairs
      cert.coeffDominant_ne_zero cert.lambdaDominant_ne_zero
      cert.tail_spectral_ratio_le cert.q_nonneg cert.q_lt_one

/-- A nonzero scalar multiple of a right eigenvector is the same right
eigenvector direction. -/
theorem isRightEigenpair_smul
    {n : ℕ} {A : Fin n → Fin n → ℝ} {lambda : ℝ} {x : Fin n → ℝ}
    (hx : IsRightEigenpair n A lambda x) {c : ℝ} (hc : c ≠ 0) :
    IsRightEigenpair n A lambda (fun i => c * x i) := by
  rcases hx.1 with ⟨i0, hi0⟩
  refine ⟨⟨i0, mul_ne_zero hc hi0⟩, ?_⟩
  intro i
  rw [matMulVec_smul_right]
  rw [hx.2 i]
  ring

/-- Exact version of the "harmless direction" part of the inverse-iteration
discussion: if the shifted-solve error is parallel to the required eigenvector,
then the returned vector is still in that eigenvector direction, provided the
resulting scalar is nonzero. This does not prove that floating-point solve
errors are parallel; it records why such an error is harmless once supplied. -/
theorem inverseIteration_parallel_error_output_isRightEigenpair
    {n : ℕ} {A : Fin n → Fin n → ℝ} {lambda mu : ℝ}
    {x err : Fin n → ℝ} (hx : IsRightEigenpair n A lambda x)
    (eta : ℝ) (herr : err = fun i => eta * x i)
    (hcoeff : (lambda - mu)⁻¹ + eta ≠ 0) :
    IsRightEigenpair n A lambda
      (fun i => (lambda - mu)⁻¹ * x i + err i) := by
  have hout :
      (fun i => (lambda - mu)⁻¹ * x i + err i) =
        fun i => ((lambda - mu)⁻¹ + eta) * x i := by
    ext i
    rw [herr]
    ring
  rw [hout]
  exact isRightEigenpair_smul hx hcoeff

/-- Eigen-residual vector `A*y - lambda*y`.  This is zero exactly on exact
right-eigenvector directions, and is the quantity controlled by the
near-parallel inverse-iteration bridge below. -/
noncomputable def eigenResidualVec (n : ℕ) (A : Fin n → Fin n → ℝ)
    (lambda : ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => matMulVec n A y i - lambda * y i

/-- Adding any scalar multiple of an exact right eigenvector does not change
the eigen-residual of the nonparallel component. -/
theorem eigenResidualVec_add_parallel_eq
    {n : ℕ} {A : Fin n → Fin n → ℝ} {lambda : ℝ}
    {x r : Fin n → ℝ} (hx : IsRightEigenpair n A lambda x) (c : ℝ) :
    eigenResidualVec n A lambda (fun i => c * x i + r i) =
      eigenResidualVec n A lambda r := by
  ext i
  unfold eigenResidualVec matMulVec
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hsum :
      (∑ j : Fin n, A i j * (c * x j)) =
        c * ∑ j : Fin n, A i j * x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hx_i : (∑ j : Fin n, A i j * x j) = lambda * x i := by
    simpa [matMulVec] using hx.2 i
  rw [hsum, hx_i]
  ring

/-- Operator-norm bound for the eigen-residual of any vector. -/
theorem eigenResidualVec_norm_le_opNorm_add_abs
    {n : ℕ} (A : Fin n → Fin n → ℝ) (lambda A_norm : ℝ)
    (r : Fin n → ℝ) (hA : opNorm2Le A A_norm) :
    vecNorm2 (eigenResidualVec n A lambda r) ≤
      (A_norm + |lambda|) * vecNorm2 r := by
  unfold eigenResidualVec
  have htri :
      vecNorm2 (fun i => matMulVec n A r i - lambda * r i) ≤
        vecNorm2 (matMulVec n A r) + vecNorm2 (fun i => (-lambda) * r i) := by
    simpa [sub_eq_add_neg, neg_mul] using
      (vecNorm2_add_le (matMulVec n A r) (fun i => (-lambda) * r i))
  have hsmul : vecNorm2 (fun i => (-lambda) * r i) = |lambda| * vecNorm2 r := by
    rw [vecNorm2_smul]
    simp
  calc
    vecNorm2 (fun i => matMulVec n A r i - lambda * r i)
        ≤ vecNorm2 (matMulVec n A r) + vecNorm2 (fun i => (-lambda) * r i) :=
          htri
    _ ≤ A_norm * vecNorm2 r + |lambda| * vecNorm2 r := by
          exact add_le_add (hA r) (le_of_eq hsmul)
    _ = (A_norm + |lambda|) * vecNorm2 r := by ring

/-- Near-parallel inverse-iteration bridge: if the shifted-solve error splits
as a harmless parallel component plus a residual component `r`, then the
eigen-residual of the returned vector depends only on `r`. -/
theorem inverseIteration_near_parallel_error_eigenResidual_eq
    {n : ℕ} {A : Fin n → Fin n → ℝ} {lambda mu : ℝ}
    {x err r : Fin n → ℝ} (hx : IsRightEigenpair n A lambda x)
    (eta : ℝ) (herr : err = fun i => eta * x i + r i) :
    eigenResidualVec n A lambda
        (fun i => (lambda - mu)⁻¹ * x i + err i) =
      eigenResidualVec n A lambda r := by
  subst err
  have hfun :
      (fun i => (lambda - mu)⁻¹ * x i + (eta * x i + r i)) =
        fun i => ((lambda - mu)⁻¹ + eta) * x i + r i := by
    ext i
    ring
  have h :=
    eigenResidualVec_add_parallel_eq
      (n := n) (A := A) (lambda := lambda) (x := x) (r := r)
      hx ((lambda - mu)⁻¹ + eta)
  simpa [hfun] using h

/-- Quantitative near-parallel inverse-iteration bridge: after decomposing the
shifted-solve error into a parallel part and residual `r`, the returned vector's
eigen-residual is bounded by `(||A||₂ + |lambda|) ||r||₂` under the repository's
operator-2 predicate surface.  A concrete floating-point shifted solve still
has to supply the decomposition and a bound on `r`. -/
theorem inverseIteration_near_parallel_error_eigenResidual_norm_le
    {n : ℕ} {A : Fin n → Fin n → ℝ} {lambda mu A_norm : ℝ}
    {x err r : Fin n → ℝ} (hx : IsRightEigenpair n A lambda x)
    (eta : ℝ) (herr : err = fun i => eta * x i + r i)
    (hA : opNorm2Le A A_norm) :
    vecNorm2
        (eigenResidualVec n A lambda
          (fun i => (lambda - mu)⁻¹ * x i + err i)) ≤
      (A_norm + |lambda|) * vecNorm2 r := by
  rw [inverseIteration_near_parallel_error_eigenResidual_eq hx eta herr]
  exact eigenResidualVec_norm_le_opNorm_add_abs A lambda A_norm r hA

/-- The §1.15 power-method example matrix. -/
noncomputable def beneficialPowerMatrix : Fin 3 → Fin 3 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => 2 / 5
  | ⟨0, _⟩, ⟨1, _⟩ => -3 / 5
  | ⟨0, _⟩, ⟨2, _⟩ => 1 / 5
  | ⟨1, _⟩, ⟨0, _⟩ => -3 / 10
  | ⟨1, _⟩, ⟨1, _⟩ => 7 / 10
  | ⟨1, _⟩, ⟨2, _⟩ => -2 / 5
  | ⟨2, _⟩, ⟨0, _⟩ => -1 / 10
  | ⟨2, _⟩, ⟨1, _⟩ => -2 / 5
  | ⟨2, _⟩, ⟨2, _⟩ => 1 / 2

/-- The displayed §1.15 matrix with each entry rounded to the repository's
finite IEEE-double round-to-even model. -/
noncomputable def beneficialPowerMatrixIeeeDoubleRounded :
    Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven
      (beneficialPowerMatrix i j)

/-- The displayed matrix entry `(1,3)` is the nonterminating binary fraction
`1/5`. -/
theorem beneficialPowerMatrix_entry_zero_two_eq_one_fifth :
    beneficialPowerMatrix 0 2 = 1 / 5 := by
  norm_num [beneficialPowerMatrix]

/-- The displayed matrix entry `(1,3)` cannot be stored exactly as a terminating
binary fraction. -/
theorem beneficialPowerMatrix_entry_zero_two_not_binaryTerminating :
    ¬ BinaryTerminating (beneficialPowerMatrix 0 2) := by
  simpa [beneficialPowerMatrix_entry_zero_two_eq_one_fifth] using
    one_fifth_not_binaryTerminating

/-- The displayed matrix entry `(1,3)` is not exactly an IEEE-double finite
value. -/
theorem beneficialPowerMatrix_entry_zero_two_not_ieeeDoubleFiniteSystem :
    ¬ FloatingPointFormat.finiteSystem FloatingPointFormat.ieeeDoubleFormat
        (beneficialPowerMatrix 0 2) := by
  simpa [beneficialPowerMatrix_entry_zero_two_eq_one_fifth] using
    one_fifth_not_ieeeDoubleFiniteSystem

/-- The displayed §1.15 matrix is not exactly storable entrywise in binary:
at least one displayed entry is not a terminating binary fraction. -/
theorem beneficialPowerMatrix_not_matrixEntriesBinaryTerminating :
    ¬ MatrixEntriesBinaryTerminating beneficialPowerMatrix := by
  intro h
  exact beneficialPowerMatrix_entry_zero_two_not_binaryTerminating (h 0 2)

/-- The displayed §1.15 matrix is not exactly storable entrywise in the
repository's IEEE-double finite system. -/
theorem beneficialPowerMatrix_not_matrixEntriesIeeeDoubleFiniteSystem :
    ¬ MatrixEntriesFiniteSystem FloatingPointFormat.ieeeDoubleFormat
        beneficialPowerMatrix := by
  intro h
  exact beneficialPowerMatrix_entry_zero_two_not_ieeeDoubleFiniteSystem (h 0 2)

/-- The displayed starting vector `[1,1,1]^T`. -/
noncomputable def beneficialPowerStart : Fin 3 → ℝ :=
  fun _ => 1

/-- The concrete §1.15 certificate target for the entrywise IEEE-double stored
matrix and displayed start vector.  Supplying this certificate is the remaining
stored-matrix spectral/eigencomponent obligation; the finite-tail convergence
theorem then applies automatically. -/
noncomputable abbrev BeneficialPowerStoredStartDominantComponentCertificate
    (m : ℕ) : Type :=
  PowerMethodDominantFiniteTailCertificate 3 m
    beneficialPowerMatrixIeeeDoubleRounded beneficialPowerStart

/-- If the remaining §1.15 stored-matrix dominant-component certificate is
supplied, the displayed start vector's scaled power-method residual for the
entrywise IEEE-double stored matrix tends to zero.  This is an implementation
handoff theorem, not a proof that the certificate holds. -/
theorem beneficialPowerStoredStart_dominant_component_certificate_scaled_residual_tendsto_zero
    {m : ℕ}
    (cert : BeneficialPowerStoredStartDominantComponentCertificate m) :
    Tendsto
      (fun k : ℕ =>
        vecNorm2
            (fun i =>
              powerMethodIterate 3 beneficialPowerMatrixIeeeDoubleRounded k
                  beneficialPowerStart i -
                cert.coeffDominant * cert.lambdaDominant ^ k *
                  cert.vDominant i) /
          |cert.coeffDominant * cert.lambdaDominant ^ k|)
      atTop (𝓝 0) :=
  cert.scaled_residual_tendsto_zero

/-- The exact first-step vector produced by entrywise IEEE-double storage of
the displayed §1.15 matrix, before any subsequent normalization. -/
noncomputable def beneficialPowerMatrixIeeeDoubleRoundedFirstStep : Fin 3 → ℝ
  | ⟨0, _⟩ => (1 : ℝ) / (2 : ℝ) ^ 54
  | ⟨1, _⟩ => -((1 : ℝ) / (2 : ℝ) ^ 54)
  | ⟨2, _⟩ => -((1 : ℝ) / (2 : ℝ) ^ 55)

/-- A concrete left-to-right rounded row-sum trace for the first multiplication
by `[1,1,1]^T` after entrywise IEEE-double storage.  Multiplication by the
exact entries of the start vector is suppressed because all start entries are
`1`; this definition isolates the rounded additions in the row sums. -/
noncomputable def beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight :
    Fin 3 → ℝ :=
  fun i =>
    let fmt := FloatingPointFormat.ieeeDoubleFormat
    let s01 := fmt.finiteRoundToEvenOp BasicOp.add
      (beneficialPowerMatrixIeeeDoubleRounded i 0)
      (beneficialPowerMatrixIeeeDoubleRounded i 1)
    fmt.finiteRoundToEvenOp BasicOp.add s01
      (beneficialPowerMatrixIeeeDoubleRounded i 2)

private theorem beneficialPowerMatrixIeeeDoubleRounded_leftToRight_row_two_first_add_eq :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        (beneficialPowerMatrixIeeeDoubleRounded 2 0)
        (beneficialPowerMatrixIeeeDoubleRounded 2 1) =
      -(1 / 2 : ℝ) := by
  unfold beneficialPowerMatrixIeeeDoubleRounded
  simp [beneficialPowerMatrix, ieeeDoubleFormat_neg_one_tenth_rounds_to,
    ieeeDoubleFormat_neg_two_fifths_rounds_to]
  simp [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact]
  convert ieeeDoubleFormat_neg_half_plus_two_pow_neg55_rounds_to_neg_half using 1 <;>
    norm_num [zpow_neg]

/-- In a left-to-right rounded-add row-sum trace, the third component cancels
to zero after the first rounded add has produced exactly `-1/2`.  This shows
that the hidden MATLAB/BLAS operation order matters: the entrywise-stored exact
row sum is `-2^-55`, but this particular rounded-add trace loses it. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight_two_component_eq_zero :
    beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight 2 = 0 := by
  unfold beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight
  change FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
      (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        (beneficialPowerMatrixIeeeDoubleRounded 2 0)
        (beneficialPowerMatrixIeeeDoubleRounded 2 1))
      (beneficialPowerMatrixIeeeDoubleRounded 2 2) = 0
  rw [beneficialPowerMatrixIeeeDoubleRounded_leftToRight_row_two_first_add_eq]
  simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix]
  rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num,
    ieeeDoubleFormat_one_half_rounds_to]
  have hfinite :
      FloatingPointFormat.ieeeDoubleFormat.finiteSystem
        (BasicOp.exact BasicOp.add (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) := by
    simpa [BasicOp.exact] using
      (FloatingPointFormat.ieeeDoubleFormat.finiteSystem_zero)
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite]
  norm_num [BasicOp.exact]
  rfl

/-- The concrete left-to-right rounded-add trace is not identical to the
entrywise-stored exact row-sum vector: its third component is zero, while the
entrywise row sum is `-2^-55`. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight_ne_firstStep :
    beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight ≠
      beneficialPowerMatrixIeeeDoubleRoundedFirstStep := by
  intro h
  have hcomp := congr_fun h (2 : Fin 3)
  rw [beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight_two_component_eq_zero]
    at hcomp
  norm_num [beneficialPowerMatrixIeeeDoubleRoundedFirstStep] at hcomp

private theorem ieeeDoubleFormat_normalizedValue_finiteSystem
    (negative : Bool) {m : ℕ} {e : ℤ}
    (hm : FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa m)
    (he : FloatingPointFormat.ieeeDoubleFormat.exponentInRange e) :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem
      (FloatingPointFormat.ieeeDoubleFormat.normalizedValue negative m e) :=
  Or.inr (Or.inl ⟨negative, m, e, hm, he, rfl⟩)

private theorem ieeeDoubleFormat_neg_7205759403792793_two_pow_neg54_finiteSystem :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem
      (-((7205759403792793 : ℝ) * (2 : ℝ) ^ (-54 : ℤ))) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hm : fmt.normalizedMantissa 7205759403792793 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (-1 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  have hval :
      fmt.normalizedValue true 7205759403792793 (-1 : ℤ) =
        -((7205759403792793 : ℝ) * (2 : ℝ) ^ (-54 : ℤ)) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  simpa [fmt, hval] using
    (ieeeDoubleFormat_normalizedValue_finiteSystem true hm he)

private theorem ieeeDoubleFormat_5404319552844594_two_pow_neg54_finiteSystem :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem
      ((5404319552844594 : ℝ) * (2 : ℝ) ^ (-54 : ℤ)) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hm : fmt.normalizedMantissa 5404319552844594 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (-1 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  have hval :
      fmt.normalizedValue false 5404319552844594 (-1 : ℤ) =
        (5404319552844594 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  simpa [fmt, hval] using
    (ieeeDoubleFormat_normalizedValue_finiteSystem false hm he)

private theorem ieeeDoubleFormat_7205759403792792_two_pow_neg56_finiteSystem :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem
      ((7205759403792792 : ℝ) * (2 : ℝ) ^ (-56 : ℤ)) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hm : fmt.normalizedMantissa 7205759403792792 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (-3 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  have hval :
      fmt.normalizedValue false 7205759403792792 (-3 : ℤ) =
        (7205759403792792 : ℝ) * (2 : ℝ) ^ (-56 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  simpa [fmt, hval] using
    (ieeeDoubleFormat_normalizedValue_finiteSystem false hm he)

/-- A concrete right-to-left rounded row-sum trace for the first multiplication
by `[1,1,1]^T` after entrywise IEEE-double storage.  This is the same modeled
routine as the left-to-right trace, but it first adds columns `1` and `2`, then
adds column `0`. -/
noncomputable def beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft :
    Fin 3 → ℝ :=
  fun i =>
    let fmt := FloatingPointFormat.ieeeDoubleFormat
    let s12 := fmt.finiteRoundToEvenOp BasicOp.add
      (beneficialPowerMatrixIeeeDoubleRounded i 1)
      (beneficialPowerMatrixIeeeDoubleRounded i 2)
    fmt.finiteRoundToEvenOp BasicOp.add
      (beneficialPowerMatrixIeeeDoubleRounded i 0) s12

private theorem beneficialPowerMatrixIeeeDoubleRounded_rightToLeft_row_zero_first_add_eq :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        (beneficialPowerMatrixIeeeDoubleRounded 0 1)
        (beneficialPowerMatrixIeeeDoubleRounded 0 2) =
      -((7205759403792793 : ℝ) * (2 : ℝ) ^ (-54 : ℤ)) := by
  unfold beneficialPowerMatrixIeeeDoubleRounded
  simp [beneficialPowerMatrix, ieeeDoubleFormat_neg_three_fifths_rounds_to]
  rw [show ((5 : ℝ)⁻¹) = (1 / 5 : ℝ) by norm_num]
  rw [ieeeDoubleFormat_one_fifth_rounds_to]
  unfold FloatingPointFormat.finiteRoundToEvenOp
  convert
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven_eq_self_of_finiteSystem
      ieeeDoubleFormat_neg_7205759403792793_two_pow_neg54_finiteSystem
    using 1
  all_goals norm_num [BasicOp.exact, zpow_neg]

private theorem beneficialPowerMatrixIeeeDoubleRounded_rightToLeft_row_one_first_add_eq :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        (beneficialPowerMatrixIeeeDoubleRounded 1 1)
        (beneficialPowerMatrixIeeeDoubleRounded 1 2) =
      (5404319552844594 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
  unfold beneficialPowerMatrixIeeeDoubleRounded
  simp [beneficialPowerMatrix, ieeeDoubleFormat_seven_tenths_rounds_to,
    ieeeDoubleFormat_neg_two_fifths_rounds_to]
  unfold FloatingPointFormat.finiteRoundToEvenOp
  convert
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven_eq_self_of_finiteSystem
      ieeeDoubleFormat_5404319552844594_two_pow_neg54_finiteSystem
    using 1
  all_goals norm_num [BasicOp.exact, zpow_neg]

private theorem beneficialPowerMatrixIeeeDoubleRounded_rightToLeft_row_two_first_add_eq :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        (beneficialPowerMatrixIeeeDoubleRounded 2 1)
        (beneficialPowerMatrixIeeeDoubleRounded 2 2) =
      (7205759403792792 : ℝ) * (2 : ℝ) ^ (-56 : ℤ) := by
  unfold beneficialPowerMatrixIeeeDoubleRounded
  simp [beneficialPowerMatrix, ieeeDoubleFormat_neg_two_fifths_rounds_to]
  rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num,
    ieeeDoubleFormat_one_half_rounds_to]
  unfold FloatingPointFormat.finiteRoundToEvenOp
  convert
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven_eq_self_of_finiteSystem
      ieeeDoubleFormat_7205759403792792_two_pow_neg56_finiteSystem
    using 1
  all_goals norm_num [BasicOp.exact, zpow_neg]

/-- In the right-to-left rounded-add row-sum trace, the first component agrees
with the entrywise-stored exact row sum `2^-54`. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_zero_component_eq :
    beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft 0 =
      (1 : ℝ) / (2 : ℝ) ^ 54 := by
  unfold beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft
  change FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
      (beneficialPowerMatrixIeeeDoubleRounded 0 0)
      (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        (beneficialPowerMatrixIeeeDoubleRounded 0 1)
        (beneficialPowerMatrixIeeeDoubleRounded 0 2)) =
    (1 : ℝ) / (2 : ℝ) ^ 54
  rw [beneficialPowerMatrixIeeeDoubleRounded_rightToLeft_row_zero_first_add_eq]
  simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix,
    ieeeDoubleFormat_two_fifths_rounds_to]
  have hfinite :
      FloatingPointFormat.ieeeDoubleFormat.finiteSystem
        (BasicOp.exact BasicOp.add
          ((7205759403792794 : ℝ) * ((2 : ℝ) ^ 54)⁻¹)
          (-((7205759403792793 : ℝ) * ((2 : ℝ) ^ 54)⁻¹))) := by
    convert ieeeDoubleFormat_two_pow_neg54_finiteSystem using 1
    norm_num [BasicOp.exact]
  convert
    FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite
    using 1
  norm_num [BasicOp.exact]

/-- In the right-to-left rounded-add row-sum trace, the second component agrees
with the entrywise-stored exact row sum `-2^-54`. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_one_component_eq :
    beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft 1 =
      -((1 : ℝ) / (2 : ℝ) ^ 54) := by
  unfold beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft
  change FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
      (beneficialPowerMatrixIeeeDoubleRounded 1 0)
      (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        (beneficialPowerMatrixIeeeDoubleRounded 1 1)
        (beneficialPowerMatrixIeeeDoubleRounded 1 2)) =
    -((1 : ℝ) / (2 : ℝ) ^ 54)
  rw [beneficialPowerMatrixIeeeDoubleRounded_rightToLeft_row_one_first_add_eq]
  simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix,
    ieeeDoubleFormat_neg_three_tenths_rounds_to]
  have hfinite :
      FloatingPointFormat.ieeeDoubleFormat.finiteSystem
        (BasicOp.exact BasicOp.add
          (-((5404319552844595 : ℝ) * ((2 : ℝ) ^ 54)⁻¹))
          ((5404319552844594 : ℝ) * ((2 : ℝ) ^ 54)⁻¹)) := by
    convert
      (FloatingPointFormat.ieeeDoubleFormat.finiteSystem_neg
        ieeeDoubleFormat_two_pow_neg54_finiteSystem) using 1
    norm_num [BasicOp.exact]
  convert
    FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite
    using 1
  norm_num [BasicOp.exact]

/-- In the right-to-left rounded-add row-sum trace, the third component agrees
with the entrywise-stored exact row sum `-2^-55`. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_two_component_eq :
    beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft 2 =
      -((1 : ℝ) / (2 : ℝ) ^ 55) := by
  unfold beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft
  change FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
      (beneficialPowerMatrixIeeeDoubleRounded 2 0)
      (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        (beneficialPowerMatrixIeeeDoubleRounded 2 1)
        (beneficialPowerMatrixIeeeDoubleRounded 2 2)) =
    -((1 : ℝ) / (2 : ℝ) ^ 55)
  rw [beneficialPowerMatrixIeeeDoubleRounded_rightToLeft_row_two_first_add_eq]
  simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix,
    ieeeDoubleFormat_neg_one_tenth_rounds_to]
  have hfinite :
      FloatingPointFormat.ieeeDoubleFormat.finiteSystem
        (BasicOp.exact BasicOp.add
          (-((7205759403792794 : ℝ) * ((2 : ℝ) ^ 56)⁻¹))
          ((7205759403792792 : ℝ) * ((2 : ℝ) ^ 56)⁻¹)) := by
    convert
      (FloatingPointFormat.ieeeDoubleFormat.finiteSystem_neg
        ieeeDoubleFormat_two_pow_neg55_finiteSystem) using 1
    norm_num [BasicOp.exact]
  convert
    FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite
    using 1
  norm_num [BasicOp.exact]

/-- The right-to-left rounded-add trace recovers the same first-step vector as
the exact entrywise-stored row-sum model.  Together with the left-to-right
caveat, this makes the remaining MATLAB obligation an explicit operation-order
question. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_eq_firstStep :
    beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft =
      beneficialPowerMatrixIeeeDoubleRoundedFirstStep := by
  ext i
  fin_cases i
  · exact beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_zero_component_eq
  · exact beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_one_component_eq
  · exact beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_two_component_eq

/-- The first row of the IEEE-double stored §1.15 matrix has a concrete
nonzero row sum.  This is the source of the first nonzero rounded power-method
component in the displayed example. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_row_zero_sum_eq :
    ∑ j : Fin 3, beneficialPowerMatrixIeeeDoubleRounded 0 j =
      (1 : ℝ) / (2 : ℝ) ^ 54 := by
  rw [Fin.sum_univ_three]
  simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix,
    ieeeDoubleFormat_two_fifths_rounds_to,
    ieeeDoubleFormat_neg_three_fifths_rounds_to]
  rw [show ((5 : ℝ)⁻¹) = (1 / 5 : ℝ) by norm_num]
  rw [ieeeDoubleFormat_one_fifth_rounds_to]
  norm_num [zpow_neg]

/-- The second row of the IEEE-double stored §1.15 matrix has the opposite
`2^-54` row sum. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_row_one_sum_eq :
    ∑ j : Fin 3, beneficialPowerMatrixIeeeDoubleRounded 1 j =
      -((1 : ℝ) / (2 : ℝ) ^ 54) := by
  rw [Fin.sum_univ_three]
  simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix,
    ieeeDoubleFormat_neg_three_tenths_rounds_to,
    ieeeDoubleFormat_seven_tenths_rounds_to,
    ieeeDoubleFormat_neg_two_fifths_rounds_to]
  norm_num [zpow_neg]

/-- The third row of the IEEE-double stored §1.15 matrix has row sum
`-2^-55`. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_row_two_sum_eq :
    ∑ j : Fin 3, beneficialPowerMatrixIeeeDoubleRounded 2 j =
      -((1 : ℝ) / (2 : ℝ) ^ 55) := by
  rw [Fin.sum_univ_three]
  simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix,
    ieeeDoubleFormat_neg_one_tenth_rounds_to,
    ieeeDoubleFormat_neg_two_fifths_rounds_to]
  rw [show ((2 : ℝ)⁻¹) = (1 / 2 : ℝ) by norm_num]
  rw [ieeeDoubleFormat_one_half_rounds_to]
  norm_num [zpow_neg]

/-- The first component of the IEEE-double stored §1.15 power-method step is
exactly `2^-54`, rather than zero. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_firstStep_zero_component_eq :
    powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
        beneficialPowerStart 0 =
      (1 : ℝ) / (2 : ℝ) ^ 54 := by
  calc
    powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
        beneficialPowerStart 0
        = ∑ j : Fin 3, beneficialPowerMatrixIeeeDoubleRounded 0 j := by
          simp [powerMethodStep, matMulVec, beneficialPowerStart]
    _ = (1 : ℝ) / (2 : ℝ) ^ 54 :=
          beneficialPowerMatrixIeeeDoubleRounded_row_zero_sum_eq

/-- The second component of the IEEE-double stored §1.15 power-method step is
exactly `-2^-54`. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_firstStep_one_component_eq :
    powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
        beneficialPowerStart 1 =
      -((1 : ℝ) / (2 : ℝ) ^ 54) := by
  calc
    powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
        beneficialPowerStart 1
        = ∑ j : Fin 3, beneficialPowerMatrixIeeeDoubleRounded 1 j := by
          simp [powerMethodStep, matMulVec, beneficialPowerStart]
    _ = -((1 : ℝ) / (2 : ℝ) ^ 54) :=
          beneficialPowerMatrixIeeeDoubleRounded_row_one_sum_eq

/-- The third component of the IEEE-double stored §1.15 power-method step is
exactly `-2^-55`. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_firstStep_two_component_eq :
    powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
        beneficialPowerStart 2 =
      -((1 : ℝ) / (2 : ℝ) ^ 55) := by
  calc
    powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
        beneficialPowerStart 2
        = ∑ j : Fin 3, beneficialPowerMatrixIeeeDoubleRounded 2 j := by
          simp [powerMethodStep, matMulVec, beneficialPowerStart]
    _ = -((1 : ℝ) / (2 : ℝ) ^ 55) :=
          beneficialPowerMatrixIeeeDoubleRounded_row_two_sum_eq

/-- Full first-step vector produced by entrywise IEEE-double storage of the
displayed §1.15 matrix. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_firstStep_eq :
    powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
        beneficialPowerStart =
      beneficialPowerMatrixIeeeDoubleRoundedFirstStep := by
  ext i
  fin_cases i
  · exact beneficialPowerMatrixIeeeDoubleRounded_firstStep_zero_component_eq
  · exact beneficialPowerMatrixIeeeDoubleRounded_firstStep_one_component_eq
  · exact beneficialPowerMatrixIeeeDoubleRounded_firstStep_two_component_eq

/-- Source-scale certificate for the §1.15 MATLAB sentence that the first
rounded power-method vector has entries of order `10^-16`: every component of
the concrete IEEE-double entrywise-storage first step has magnitude between
`10^-17` and `10^-16`. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_firstStep_abs_between_one_e17_one_e16
    (i : Fin 3) :
    (1 : ℝ) / (10 : ℝ) ^ 17 ≤
        |powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
          beneficialPowerStart i| ∧
      |powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
          beneficialPowerStart i| ≤
        (1 : ℝ) / (10 : ℝ) ^ 16 := by
  rw [beneficialPowerMatrixIeeeDoubleRounded_firstStep_eq]
  fin_cases i <;>
    norm_num [beneficialPowerMatrixIeeeDoubleRoundedFirstStep]

/-- The characteristic matrix `lambda I - A` for the §1.15 power-method
example. -/
noncomputable def beneficialPowerCharMatrix (lambda : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (if i = j then lambda else 0) - beneficialPowerMatrix i j

/-- Every row of the §1.15 matrix sums to zero. -/
theorem beneficialPowerMatrix_row_sum_zero (i : Fin 3) :
    ∑ j : Fin 3, beneficialPowerMatrix i j = 0 := by
  fin_cases i <;> rw [Fin.sum_univ_three] <;> norm_num [beneficialPowerMatrix]

/-- The characteristic determinant of the displayed §1.15 matrix. -/
theorem beneficialPowerCharDet_eq (lambda : ℝ) :
    Matrix.det (beneficialPowerCharMatrix lambda) =
      lambda * (lambda ^ 2 - (8 / 5) * lambda + 51 / 100) := by
  rw [Matrix.det_fin_three]
  simp [beneficialPowerCharMatrix]
  norm_num [beneficialPowerMatrix]
  ring_nf

/-- The zero eigenvalue appears as a root of the characteristic determinant. -/
theorem beneficialPowerCharDet_root_zero :
    Matrix.det (beneficialPowerCharMatrix 0) = 0 := by
  rw [beneficialPowerCharDet_eq]
  ring

/-- The smaller nonzero exact eigenvalue in the §1.15 display. -/
theorem beneficialPowerCharDet_root_small :
    Matrix.det (beneficialPowerCharMatrix (4 / 5 - Real.sqrt 13 / 10)) = 0 := by
  rw [beneficialPowerCharDet_eq]
  have hsq : (Real.sqrt (13 : ℝ)) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- The dominant exact eigenvalue in the §1.15 display. -/
theorem beneficialPowerCharDet_root_dominant :
    Matrix.det (beneficialPowerCharMatrix (4 / 5 + Real.sqrt 13 / 10)) = 0 := by
  rw [beneficialPowerCharDet_eq]
  have hsq : (Real.sqrt (13 : ℝ)) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- The smaller nonzero eigenvalue is within one half-unit in the last
displayed decimal place of the source value `0.4394`. -/
theorem beneficialPowerEigenvalueSmall_display_accuracy :
    |(4 / 5 - Real.sqrt 13 / 10 : ℝ) - 4394 / 10000| < 1 / 20000 := by
  have hsqrt_lo : (36055 : ℝ) / 10000 < Real.sqrt 13 :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  have hsqrt_hi : Real.sqrt 13 < (3606 : ℝ) / 1000 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  rw [abs_lt]
  constructor <;> nlinarith

/-- The dominant eigenvalue is within one half-unit in the last displayed
decimal place of the source value `1.161`. -/
theorem beneficialPowerEigenvalueDominant_display_accuracy :
    |(4 / 5 + Real.sqrt 13 / 10 : ℝ) - 1161 / 1000| < 1 / 2000 := by
  have hsqrt_lo : (36055 : ℝ) / 10000 < Real.sqrt 13 :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  have hsqrt_hi : Real.sqrt 13 < (3606 : ℝ) / 1000 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  rw [abs_lt]
  constructor <;> nlinarith

/-- The displayed starting vector is a right eigenvector for eigenvalue zero. -/
theorem beneficialPowerStart_isRightEigenpair_zero :
    IsRightEigenpair 3 beneficialPowerMatrix 0 beneficialPowerStart := by
  refine ⟨?_, ?_⟩
  · exact ⟨0, by norm_num [beneficialPowerStart]⟩
  · intro i
    calc matMulVec 3 beneficialPowerMatrix beneficialPowerStart i
        = ∑ j : Fin 3, beneficialPowerMatrix i j := by
            unfold matMulVec beneficialPowerStart
            simp
      _ = 0 := beneficialPowerMatrix_row_sum_zero i
      _ = 0 * beneficialPowerStart i := by simp

/-- In exact arithmetic the first unnormalized power-method step is zero. -/
theorem beneficialPowerFirstStep_zero :
    powerMethodStep 3 beneficialPowerMatrix beneficialPowerStart =
      fun _ : Fin 3 => 0 := by
  ext i
  unfold powerMethodStep
  simpa [beneficialPowerStart] using (beneficialPowerStart_isRightEigenpair_zero).2 i

/-- For the displayed zero-eigenvector start, the shifted matrix maps the start
vector to `-mu` times the same vector. -/
theorem beneficialPowerShiftedMatrix_mul_start (mu : ℝ) (i : Fin 3) :
    matMulVec 3 (inverseIterationShiftedMatrix 3 beneficialPowerMatrix mu)
        beneficialPowerStart i =
      (-mu) * beneficialPowerStart i := by
  simpa using
    (inverseIteration_shiftedMatrix_mul_eigenvector
      (n := 3) (A := beneficialPowerMatrix) (lambda := 0) (mu := mu)
      (x := beneficialPowerStart) beneficialPowerStart_isRightEigenpair_zero i)

/-- Concrete exact inverse-iteration shifted solve for the displayed §1.15
start vector and the zero eigenvalue. -/
theorem beneficialPower_inverseIteration_shiftedSystem_solution_start
    {mu : ℝ} (hmu : mu ≠ 0) :
    SolvesInverseIterationShiftedSystem 3 beneficialPowerMatrix mu
      beneficialPowerStart (fun i => (-mu)⁻¹ * beneficialPowerStart i) := by
  have hshift : (0 : ℝ) - mu ≠ 0 := by
    simpa using neg_ne_zero.mpr hmu
  simpa using
    (inverseIteration_shiftedSystem_solution_on_eigenvector
      (n := 3) (A := beneficialPowerMatrix) (lambda := 0) (mu := mu)
      (x := beneficialPowerStart) beneficialPowerStart_isRightEigenpair_zero
      hshift)

/-- Any left inverse of the displayed shifted matrix acts on the displayed start
vector by the exact scalar `(-mu)^{-1}`. -/
theorem beneficialPower_shiftedInverse_mul_start_of_leftInverse
    {mu : ℝ} {B : Fin 3 → Fin 3 → ℝ} (hmu : mu ≠ 0)
    (hB : IsLeftInverse 3
      (inverseIterationShiftedMatrix 3 beneficialPowerMatrix mu) B) :
    matMulVec 3 B beneficialPowerStart =
      fun i => (-mu)⁻¹ * beneficialPowerStart i := by
  have hshift : (0 : ℝ) - mu ≠ 0 := by
    simpa using neg_ne_zero.mpr hmu
  simpa using
    (inverseIteration_shiftedInverse_mul_eigenvector_of_leftInverse
      (n := 3) (A := beneficialPowerMatrix) (B := B)
      (lambda := 0) (mu := mu) (x := beneficialPowerStart)
      beneficialPowerStart_isRightEigenpair_zero hshift hB)

/-- Displayed §1.15 near-parallel inverse-iteration bridge: for Higham's
matrix and start vector, the eigen-residual of the shifted inverse-iteration
output depends only on the nonparallel residual component. -/
theorem beneficialPower_inverseIteration_near_parallel_error_eigenResidual_eq
    {mu eta : ℝ} {err r : Fin 3 → ℝ}
    (herr : err = fun i => eta * beneficialPowerStart i + r i) :
    eigenResidualVec 3 beneficialPowerMatrix 0
        (fun i => (-mu)⁻¹ * beneficialPowerStart i + err i) =
      eigenResidualVec 3 beneficialPowerMatrix 0 r := by
  simpa using
    (inverseIteration_near_parallel_error_eigenResidual_eq
      (n := 3) (A := beneficialPowerMatrix) (lambda := 0) (mu := mu)
      (x := beneficialPowerStart) (err := err) (r := r)
      beneficialPowerStart_isRightEigenpair_zero eta herr)

/-- Displayed §1.15 quantitative near-parallel bridge: for Higham's matrix and
start vector, only the nonparallel residual component contributes to the
eigen-residual norm. -/
theorem beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le
    {mu eta A_norm : ℝ} {err r : Fin 3 → ℝ}
    (herr : err = fun i => eta * beneficialPowerStart i + r i)
    (hA : opNorm2Le beneficialPowerMatrix A_norm) :
    vecNorm2
        (eigenResidualVec 3 beneficialPowerMatrix 0
          (fun i => (-mu)⁻¹ * beneficialPowerStart i + err i)) ≤
      A_norm * vecNorm2 r := by
  simpa using
    (inverseIteration_near_parallel_error_eigenResidual_norm_le
      (n := 3) (A := beneficialPowerMatrix) (lambda := 0) (mu := mu)
      (A_norm := A_norm) (x := beneficialPowerStart) (err := err) (r := r)
      beneficialPowerStart_isRightEigenpair_zero eta herr hA)

/-- Residual-budget form of the displayed §1.15 near-parallel bridge. -/
theorem beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le_of_residual_norm_le
    {mu eta A_norm eps : ℝ} {err r : Fin 3 → ℝ}
    (herr : err = fun i => eta * beneficialPowerStart i + r i)
    (hA : opNorm2Le beneficialPowerMatrix A_norm) (hA_nonneg : 0 ≤ A_norm)
    (hr : vecNorm2 r ≤ eps) :
    vecNorm2
        (eigenResidualVec 3 beneficialPowerMatrix 0
          (fun i => (-mu)⁻¹ * beneficialPowerStart i + err i)) ≤
      A_norm * eps := by
  exact le_trans
    (beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le
      (mu := mu) (eta := eta) (A_norm := A_norm) (err := err) (r := r)
      herr hA)
    (mul_le_mul_of_nonneg_left hr hA_nonneg)

/-- Componentwise near-parallel certificate for the displayed §1.15 inverse
iteration example.  If every shifted-solve error component is within `eps` of
one common scalar `eta`, then the error splits into a harmless multiple of the
displayed eigenvector plus a residual of norm at most `sqrt 3 * eps`, and the
existing near-parallel residual bound applies. -/
theorem
    beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le_of_componentwise_common_scalar
    {mu eta A_norm eps : ℝ} {err : Fin 3 → ℝ}
    (hA : opNorm2Le beneficialPowerMatrix A_norm) (hA_nonneg : 0 ≤ A_norm)
    (heps_nonneg : 0 ≤ eps)
    (herr : ∀ i : Fin 3, |err i - eta| ≤ eps) :
    vecNorm2
        (eigenResidualVec 3 beneficialPowerMatrix 0
          (fun i => (-mu)⁻¹ * beneficialPowerStart i + err i)) ≤
      A_norm * (Real.sqrt (3 : ℝ) * eps) := by
  let r : Fin 3 → ℝ := fun i => err i - eta * beneficialPowerStart i
  have hdecomp : err = fun i => eta * beneficialPowerStart i + r i := by
    ext i
    dsimp [r]
    ring
  have hr_abs : ∀ i : Fin 3, |r i| ≤ eps := by
    intro i
    simpa [r, beneficialPowerStart] using herr i
  have hr_norm : vecNorm2 r ≤ Real.sqrt (3 : ℝ) * eps := by
    simpa using
      (vecNorm2_le_sqrt_card_mul_of_abs_le (n := 3) r heps_nonneg hr_abs)
  exact
    beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le_of_residual_norm_le
      (mu := mu) (eta := eta) (A_norm := A_norm)
      (eps := Real.sqrt (3 : ℝ) * eps) (err := err) (r := r)
      hdecomp hA hA_nonneg hr_norm

/-- A first power-method step with a perturbed stored matrix splits into the
exact step plus the perturbation action. -/
theorem powerMethodStep_add_matrix (n : ℕ) (A ΔA : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) :
    powerMethodStep n (fun i j => A i j + ΔA i j) x =
      fun i => powerMethodStep n A x i + matMulVec n ΔA x i := by
  ext i
  unfold powerMethodStep matMulVec
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- For the displayed example, the first step with a stored perturbation is
exactly the action of the perturbation on `[1,1,1]^T`. -/
theorem beneficialPowerFirstStep_perturbed_eq_delta
    (ΔA : Fin 3 → Fin 3 → ℝ) :
    powerMethodStep 3 (fun i j => beneficialPowerMatrix i j + ΔA i j)
        beneficialPowerStart =
      matMulVec 3 ΔA beneficialPowerStart := by
  rw [powerMethodStep_add_matrix]
  ext i
  rw [beneficialPowerFirstStep_zero]
  simp

/-- Exact zero-characterization for the displayed §1.15 perturbed first
power-method step: row sums of the stored perturbation are the whole
first-step obstruction. -/
theorem beneficialPowerFirstStep_perturbed_eq_zero_iff_row_sums_zero
    (ΔA : Fin 3 → Fin 3 → ℝ) :
    powerMethodStep 3 (fun i j => beneficialPowerMatrix i j + ΔA i j)
        beneficialPowerStart = (fun _ => 0) ↔
      ∀ i : Fin 3, ∑ j : Fin 3, ΔA i j = 0 := by
  rw [beneficialPowerFirstStep_perturbed_eq_delta]
  constructor
  · intro h i
    have hi := congrFun h i
    simpa [matMulVec, beneficialPowerStart] using hi
  · intro h
    funext i
    simpa [matMulVec, beneficialPowerStart] using h i

/-- If the stored perturbation has a nonzero row sum, then the first perturbed
power-method step is nonzero in that component. -/
theorem beneficialPowerFirstStep_perturbed_nonzero_of_delta_row_sum_ne_zero
    (ΔA : Fin 3 → Fin 3 → ℝ) {i : Fin 3}
    (hi : (∑ j : Fin 3, ΔA i j) ≠ 0) :
    ∃ i : Fin 3,
      powerMethodStep 3 (fun i j => beneficialPowerMatrix i j + ΔA i j)
        beneficialPowerStart i ≠ 0 := by
  refine ⟨i, ?_⟩
  rw [beneficialPowerFirstStep_perturbed_eq_delta]
  simpa [matMulVec, beneficialPowerStart] using hi

/-- A vector with a nonzero component has positive Euclidean norm. -/
theorem vecNorm2_pos_of_exists_ne {n : ℕ} {x : Fin n → ℝ}
    (h : ∃ i : Fin n, x i ≠ 0) :
    0 < vecNorm2 x := by
  have hnonneg : 0 ≤ vecNorm2 x := vecNorm2_nonneg x
  exact lt_of_le_of_ne hnonneg (by
    intro hzero
    rcases h with ⟨i, hi⟩
    exact hi ((vecNorm2_eq_zero_iff x).mp hzero.symm i))

/-- The IEEE-double stored §1.15 matrix restarts the first power-method step:
the first-step vector has positive Euclidean norm because its first component
is exactly `2^-54`. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_firstStep_vecNorm2_pos :
    0 < vecNorm2
      (powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
        beneficialPowerStart) := by
  exact vecNorm2_pos_of_exists_ne
    ⟨0, by
      rw [beneficialPowerMatrixIeeeDoubleRounded_firstStep_zero_component_eq]
      positivity⟩

/-- Concrete lower bound for the IEEE-double stored §1.15 first-step norm. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_firstStep_vecNorm2_ge_two_pow_neg54 :
    (1 : ℝ) / (2 : ℝ) ^ 54 ≤
      vecNorm2
        (powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
          beneficialPowerStart) := by
  have hcoord :=
    abs_coord_le_vecNorm2
      (powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
        beneficialPowerStart) 0
  have hcomponent :
      |powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
          beneficialPowerStart 0| =
        (1 : ℝ) / (2 : ℝ) ^ 54 := by
    rw [beneficialPowerMatrixIeeeDoubleRounded_firstStep_zero_component_eq]
    exact abs_of_pos (by positivity)
  simpa [hcomponent] using hcoord

/-- Norm-level version of the §1.15 perturbation restart: if the stored
matrix perturbation has a nonzero row sum, then the first perturbed power
method step is not merely componentwise nonzero; it has positive Euclidean
norm. -/
theorem beneficialPowerFirstStep_perturbed_vecNorm2_pos_of_delta_row_sum_ne_zero
    (ΔA : Fin 3 → Fin 3 → ℝ) {i : Fin 3}
    (hi : (∑ j : Fin 3, ΔA i j) ≠ 0) :
    0 < vecNorm2
      (powerMethodStep 3 (fun i j => beneficialPowerMatrix i j + ΔA i j)
        beneficialPowerStart) := by
  exact vecNorm2_pos_of_exists_ne
    (beneficialPowerFirstStep_perturbed_nonzero_of_delta_row_sum_ne_zero
      ΔA hi)

/-- Norm-level zero-characterization for the displayed §1.15 perturbed first
step.  The Euclidean norm of the first perturbed vector vanishes exactly when
every stored-perturbation row sum vanishes. -/
theorem beneficialPowerFirstStep_perturbed_vecNorm2_eq_zero_iff_row_sums_zero
    (ΔA : Fin 3 → Fin 3 → ℝ) :
    vecNorm2
      (powerMethodStep 3 (fun i j => beneficialPowerMatrix i j + ΔA i j)
        beneficialPowerStart) = 0 ↔
      ∀ i : Fin 3, ∑ j : Fin 3, ΔA i j = 0 := by
  constructor
  · intro hnorm i
    rw [beneficialPowerFirstStep_perturbed_eq_delta] at hnorm
    have hzero :
        matMulVec 3 ΔA beneficialPowerStart i = 0 :=
      (vecNorm2_eq_zero_iff _).mp hnorm i
    simpa [matMulVec, beneficialPowerStart] using hzero
  · intro hrow
    apply (vecNorm2_eq_zero_iff _).mpr
    intro i
    rw [beneficialPowerFirstStep_perturbed_eq_delta]
    simpa [matMulVec, beneficialPowerStart] using hrow i

/-- Lower-bound certificate for the displayed §1.15 perturbed first step:
any row-sum magnitude of the stored perturbation is bounded above by the
Euclidean norm of the first perturbed power-method vector. -/
theorem beneficialPowerFirstStep_perturbed_vecNorm2_ge_of_row_sum_abs_ge
    (ΔA : Fin 3 → Fin 3 → ℝ) {i : Fin 3} {rho : ℝ}
    (hi : rho ≤ |∑ j : Fin 3, ΔA i j|) :
    rho ≤ vecNorm2
      (powerMethodStep 3 (fun i j => beneficialPowerMatrix i j + ΔA i j)
        beneficialPowerStart) := by
  rw [beneficialPowerFirstStep_perturbed_eq_delta]
  exact hi.trans (by
    simpa [matMulVec, beneficialPowerStart] using
      (abs_coord_le_vecNorm2 (matMulVec 3 ΔA beneficialPowerStart) i))

/-- Row-sum perturbation budget for the displayed §1.15 first power-method
step.  If every stored-perturbation row sum is bounded by `eps`, then the
first perturbed vector has Euclidean norm at most `sqrt 3 * eps`. -/
theorem beneficialPowerFirstStep_perturbed_vecNorm2_le_of_row_sum_abs_le
    (ΔA : Fin 3 → Fin 3 → ℝ) {eps : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hrow : ∀ i : Fin 3, |∑ j : Fin 3, ΔA i j| ≤ eps) :
    vecNorm2
      (powerMethodStep 3 (fun i j => beneficialPowerMatrix i j + ΔA i j)
        beneficialPowerStart) ≤ Real.sqrt (3 : ℝ) * eps := by
  rw [beneficialPowerFirstStep_perturbed_eq_delta]
  exact
    vecNorm2_le_sqrt_card_mul_of_abs_le
      (n := 3) (fun i => matMulVec 3 ΔA beneficialPowerStart i)
      heps_nonneg (by
        intro i
        simpa [matMulVec, beneficialPowerStart] using hrow i)

/-- Entrywise perturbation budget for the displayed §1.15 first power-method
step.  A uniform entrywise perturbation radius `eps` bounds each row sum by
`3*eps`, hence bounds the first perturbed vector by `sqrt 3 * (3*eps)`. -/
theorem beneficialPowerFirstStep_perturbed_vecNorm2_le_of_entry_abs_le
    (ΔA : Fin 3 → Fin 3 → ℝ) {eps : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hentry : ∀ i j : Fin 3, |ΔA i j| ≤ eps) :
    vecNorm2
      (powerMethodStep 3 (fun i j => beneficialPowerMatrix i j + ΔA i j)
        beneficialPowerStart) ≤ Real.sqrt (3 : ℝ) * (3 * eps) := by
  have hrow : ∀ i : Fin 3, |∑ j : Fin 3, ΔA i j| ≤ 3 * eps := by
    intro i
    calc
      |∑ j : Fin 3, ΔA i j| ≤ ∑ j : Fin 3, |ΔA i j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 3, eps := by
        apply Finset.sum_le_sum
        intro j _hj
        exact hentry i j
      _ = 3 * eps := by
        simp
  exact
    beneficialPowerFirstStep_perturbed_vecNorm2_le_of_row_sum_abs_le
      ΔA (by nlinarith) hrow

end LeanFpAnalysis.FP
