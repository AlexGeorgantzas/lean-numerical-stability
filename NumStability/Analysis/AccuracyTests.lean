import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.Accumulation
import NumStability.Analysis.Nonassociativity
import NumStability.Analysis.RoundingProductBounds
import NumStability.Source.Higham.Chapter02.Section11.AccuracyTests.Basic

/-!
# AccuracyTests (compatibility module)

Historical path, retained so existing imports of `NumStability.Analysis.AccuracyTests`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

noncomputable section

namespace NumStability

private theorem summable_sine_odd_terms (x : ℝ) :
    Summable
      (fun n : ℕ => x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)) := by
  simpa only [Function.comp_apply] using
    (Real.summable_pow_div_factorial x).comp_injective
      (by
        intro a b h
        have hsucc : Nat.succ (2 * a) = Nat.succ (2 * b) := by
          simpa [Nat.succ_eq_add_one] using h
        have hmul : 2 * a = 2 * b := Nat.succ.inj hsucc
        exact Nat.mul_left_cancel (by norm_num : 0 < 2) hmul)

private theorem sine_odd_terms_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone
      (fun n : ℕ => x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  have hx2 : x ^ 2 ≤ 1 := by
    have hmul := mul_le_mul hx1 hx1 hx0 zero_le_one
    nlinarith [hmul]
  have hpow : x ^ (2 * (n + 1) + 1) ≤ x ^ (2 * n + 1) := by
    have hnon : 0 ≤ x ^ (2 * n + 1) := pow_nonneg hx0 _
    calc
      x ^ (2 * (n + 1) + 1) = x ^ (2 * n + 1) * x ^ 2 := by
        have hn : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
        rw [hn, pow_add]
      _ ≤ x ^ (2 * n + 1) * 1 := mul_le_mul_of_nonneg_left hx2 hnon
      _ = x ^ (2 * n + 1) := by ring
  have hden_nonneg : 0 ≤ (Nat.factorial (2 * (n + 1) + 1) : ℝ) := by positivity
  have hden_pos : 0 < (Nat.factorial (2 * n + 1) : ℝ) := by positivity
  have hden_le :
      (Nat.factorial (2 * n + 1) : ℝ) ≤
        (Nat.factorial (2 * (n + 1) + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : 2 * n + 1 ≤ 2 * (n + 1) + 1)
  have hnum_nonneg : 0 ≤ x ^ (2 * n + 1) := pow_nonneg hx0 _
  exact (div_le_div_of_nonneg_right hpow hden_nonneg).trans
    (div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_le)

/-- Alternating-series remainder bound for the five-term odd Taylor polynomial
for `sin` on `[0, 1]`. -/
theorem sineTaylorOdd5_abs_error_le_next (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.sin x - sineTaylorOdd5 x| ≤ x ^ 11 / (Nat.factorial 11 : ℝ) := by
  let f : ℕ → ℝ :=
    fun n => x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)
  have hsummable : Summable f := by
    simpa [f] using summable_sine_odd_terms x
  have hant : Antitone f := by
    simpa [f] using sine_odd_terms_antitone (x := x) hx0 hx1
  have h := alternating_series_error_bound f hant hsummable 5
  have htsum : (∑' i : ℕ, (-1 : ℝ) ^ i * f i) = Real.sin x := by
    simpa [f, div_eq_mul_inv, mul_assoc] using (Real.hasSum_sin x).tsum_eq
  rw [htsum] at h
  have hpartial : (∑ i ∈ Finset.range 5, (-1 : ℝ) ^ i * f i) =
      sineTaylorOdd5 x := by
    simp [f, sineTaylorOdd5]
  have hnext : f 5 = x ^ 11 / (Nat.factorial 11 : ℝ) := by
    norm_num [f]
  simpa [hpartial, hnext] using h

theorem codySineReducedArgument_sineTaylorOdd5_abs_error_lt_one_e20 :
    |Real.sin codySineReducedArgument - sineTaylorOdd5 codySineReducedArgument| <
      (1 : ℝ) / 10 ^ 20 := by
  have hle := sineTaylorOdd5_abs_error_le_next codySineReducedArgument
    (le_of_lt codySineReducedArgument_pos)
    (le_trans (le_of_lt codySineReducedArgument_lt_one_hundredth)
      (by norm_num : (1 / 100 : ℝ) ≤ 1))
  have hr_nonneg : 0 ≤ codySineReducedArgument := le_of_lt codySineReducedArgument_pos
  have hr_le : codySineReducedArgument ≤ (1 / 100 : ℝ) :=
    le_of_lt codySineReducedArgument_lt_one_hundredth
  have hpow : codySineReducedArgument ^ 11 ≤ (1 / 100 : ℝ) ^ 11 :=
    pow_le_pow_left₀ hr_nonneg hr_le 11
  have hrem :
      codySineReducedArgument ^ 11 / (Nat.factorial 11 : ℝ) <
        (1 : ℝ) / 10 ^ 20 := by
    calc
      codySineReducedArgument ^ 11 / (Nat.factorial 11 : ℝ)
          ≤ (1 / 100 : ℝ) ^ 11 / (Nat.factorial 11 : ℝ) := by
              exact div_le_div_of_nonneg_right hpow (by positivity)
      _ < (1 : ℝ) / 10 ^ 20 := by norm_num
  exact lt_of_le_of_lt hle hrem

theorem codySineTestExact_sineTaylorOdd5_abs_error_lt_one_e20 :
    |codySineTestExact + sineTaylorOdd5 codySineReducedArgument| <
      (1 : ℝ) / 10 ^ 20 := by
  have h := codySineReducedArgument_sineTaylorOdd5_abs_error_lt_one_e20
  rw [codySineTestExact_eq_neg_sin_reducedArgument]
  have halg :
      -Real.sin codySineReducedArgument + sineTaylorOdd5 codySineReducedArgument =
        -(Real.sin codySineReducedArgument - sineTaylorOdd5 codySineReducedArgument) := by
    ring
  rw [halg, abs_neg]
  exact h

private def codySineReducedArgumentLowerD20 : ℝ :=
  22 - 7 * (314159265358979323847 : ℝ) / 10 ^ 20

private def codySineReducedArgumentUpperD20 : ℝ :=
  22 - 7 * (314159265358979323846 : ℝ) / 10 ^ 20

private theorem codySineReducedArgumentLowerD20_le :
    codySineReducedArgumentLowerD20 ≤ codySineReducedArgument := by
  unfold codySineReducedArgumentLowerD20 codySineReducedArgument
  nlinarith [Real.pi_lt_d20]

private theorem codySineReducedArgument_leUpperD20 :
    codySineReducedArgument ≤ codySineReducedArgumentUpperD20 := by
  unfold codySineReducedArgumentUpperD20 codySineReducedArgument
  nlinarith [Real.pi_gt_d20]

theorem codySineTaylorOdd5_displayedMagnitude_abs_error_lt_41e21 :
    |sineTaylorOdd5 codySineReducedArgument - codySineDisplayedTableMagnitude17| <
      (41 : ℝ) / 10 ^ 21 := by
  let lo : ℝ := codySineReducedArgumentLowerD20
  let hi : ℝ := codySineReducedArgumentUpperD20
  let r : ℝ := codySineReducedArgument
  let d : ℝ := codySineDisplayedTableMagnitude17
  have hlo : lo ≤ r := by
    simpa [lo, r] using codySineReducedArgumentLowerD20_le
  have hhi : r ≤ hi := by
    simpa [hi, r] using codySineReducedArgument_leUpperD20
  have hlo_nonneg : 0 ≤ lo := by
    norm_num [lo, codySineReducedArgumentLowerD20]
  have hr_nonneg : 0 ≤ r := by
    simpa [r] using le_of_lt codySineReducedArgument_pos
  have hhi_nonneg : 0 ≤ hi := by
    norm_num [hi, codySineReducedArgumentUpperD20]
  have h3lo : lo ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hlo_nonneg hlo 3
  have h5hi : r ^ 5 ≤ hi ^ 5 := pow_le_pow_left₀ hr_nonneg hhi 5
  have h7lo : lo ^ 7 ≤ r ^ 7 := pow_le_pow_left₀ hlo_nonneg hlo 7
  have h9hi : r ^ 9 ≤ hi ^ 9 := pow_le_pow_left₀ hr_nonneg hhi 9
  have h3hi : r ^ 3 ≤ hi ^ 3 := pow_le_pow_left₀ hr_nonneg hhi 3
  have h5lo : lo ^ 5 ≤ r ^ 5 := pow_le_pow_left₀ hlo_nonneg hlo 5
  have h7hi : r ^ 7 ≤ hi ^ 7 := pow_le_pow_left₀ hr_nonneg hhi 7
  have h9lo : lo ^ 9 ≤ r ^ 9 := pow_le_pow_left₀ hlo_nonneg hlo 9
  have hupper :
      sineTaylorOdd5 r - d ≤
        hi - lo ^ 3 / 6 + hi ^ 5 / 120 - lo ^ 7 / 5040 + hi ^ 9 / 362880 - d := by
    rw [sineTaylorOdd5_eq]
    nlinarith
  have hlower :
      lo - hi ^ 3 / 6 + lo ^ 5 / 120 - hi ^ 7 / 5040 + lo ^ 9 / 362880 - d ≤
        sineTaylorOdd5 r - d := by
    rw [sineTaylorOdd5_eq]
    nlinarith
  have hupper_num :
      hi - lo ^ 3 / 6 + hi ^ 5 / 120 - lo ^ 7 / 5040 + hi ^ 9 / 362880 - d <
        (41 : ℝ) / 10 ^ 21 := by
    norm_num [lo, hi, d, codySineReducedArgumentLowerD20,
      codySineReducedArgumentUpperD20, codySineDisplayedTableMagnitude17]
  have hlower_num :
      -((41 : ℝ) / 10 ^ 21) <
        lo - hi ^ 3 / 6 + lo ^ 5 / 120 - hi ^ 7 / 5040 + lo ^ 9 / 362880 - d := by
    norm_num [lo, hi, d, codySineReducedArgumentLowerD20,
      codySineReducedArgumentUpperD20, codySineDisplayedTableMagnitude17]
  rw [abs_lt]
  constructor
  · exact lt_of_lt_of_le hlower_num hlower
  · exact lt_of_le_of_lt hupper hupper_num

theorem codySineTestExact_displayedTableDecimal17_abs_error_lt_half_last_place :
    |codySineTestExact - codySineDisplayedTableDecimal17| <
      (1 / 2 : ℝ) / 10 ^ 19 := by
  have hrem_le := sineTaylorOdd5_abs_error_le_next codySineReducedArgument
    (le_of_lt codySineReducedArgument_pos)
    (le_trans (le_of_lt codySineReducedArgument_lt_one_hundredth)
      (by norm_num : (1 / 100 : ℝ) ≤ 1))
  have hr_nonneg : 0 ≤ codySineReducedArgument := le_of_lt codySineReducedArgument_pos
  have hr_le : codySineReducedArgument ≤ (1 / 100 : ℝ) :=
    le_of_lt codySineReducedArgument_lt_one_hundredth
  have hpow : codySineReducedArgument ^ 11 ≤ (1 / 100 : ℝ) ^ 11 :=
    pow_le_pow_left₀ hr_nonneg hr_le 11
  have hrem :
      |Real.sin codySineReducedArgument - sineTaylorOdd5 codySineReducedArgument| <
        (1 : ℝ) / 10 ^ 21 := by
    refine lt_of_le_of_lt hrem_le ?_
    calc
      codySineReducedArgument ^ 11 / (Nat.factorial 11 : ℝ)
          ≤ (1 / 100 : ℝ) ^ 11 / (Nat.factorial 11 : ℝ) := by
              exact div_le_div_of_nonneg_right hpow (by positivity)
      _ < (1 : ℝ) / 10 ^ 21 := by norm_num
  have hpoly := codySineTaylorOdd5_displayedMagnitude_abs_error_lt_41e21
  have htarget :
      |Real.sin codySineReducedArgument - codySineDisplayedTableMagnitude17| <
        (1 / 2 : ℝ) / 10 ^ 19 := by
    calc
      |Real.sin codySineReducedArgument - codySineDisplayedTableMagnitude17|
          =
            |(Real.sin codySineReducedArgument -
                sineTaylorOdd5 codySineReducedArgument) +
              (sineTaylorOdd5 codySineReducedArgument -
                codySineDisplayedTableMagnitude17)| := by
              ring_nf
      _ ≤ |Real.sin codySineReducedArgument - sineTaylorOdd5 codySineReducedArgument| +
            |sineTaylorOdd5 codySineReducedArgument -
              codySineDisplayedTableMagnitude17| := abs_add_le _ _
      _ < (1 : ℝ) / 10 ^ 21 + (41 : ℝ) / 10 ^ 21 :=
            add_lt_add hrem hpoly
      _ < (1 / 2 : ℝ) / 10 ^ 19 := by norm_num
  rw [codySineTestExact_eq_neg_sin_reducedArgument, codySineDisplayedTableDecimal17]
  have halg :
      -Real.sin codySineReducedArgument - -codySineDisplayedTableMagnitude17 =
        -(Real.sin codySineReducedArgument - codySineDisplayedTableMagnitude17) := by
    ring
  rw [halg, abs_neg]
  exact htarget

end NumStability

end
