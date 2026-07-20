-- Analysis/Problem2_7.lean
--
-- Finite round-to-even theorem surfaces for Higham Chapter 2, Problem 2.7.

import NumStability.Analysis.Midpoint

namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-!
# Higham Chapter 2, Problem 2.7

Problem 2.7 asks which displayed identities hold in IEEE arithmetic for
normalized finite inputs when no exception occurs.  This file records the
parts that are already faithful at the repository's ordinary finite
round-to-even operation layer:

* add and multiply commute because the exact real inputs to the final rounding
  are equal;
* `fl(b-a) = -fl(a-b)` is proved on the exact-representable subtraction
  branch, where the operation wrapper returns both exact differences;
* `fl(b-a) = -fl(a-b)` is also proved when `a-b` is outside the finite-normal
  magnitude band, using the underflow and overflow branch oddness lemmas for
  the total finite selector;
* `fl(b-a) = -fl(a-b)` is now closed for the total finite round-to-even
  selector under the binary/IEEE-style side conditions that the radix is even
  and `1 < t`;
* `fl(a + a) = fl(2*a)` for the same reason;
* `fl((1/2)*a) = fl(a/2)` for the same reason;
* the associativity and midpoint strict-between statements are false, witnessed
  by the existing Chapter 2 finite examples.

Proving the corresponding statement for full IEEE arithmetic still belongs to
the full IEEE operation layer: signed zeros, NaNs, infinities, exception flags,
traps, and concrete operation semantics remain outside this finite real-valued
selector theorem.
-/

/-- Problem 2.7 statement 1, addition case, at the ordinary finite
round-to-even layer. -/
theorem finiteRoundToEvenOp_add_comm
    (fmt : FloatingPointFormat) (a b : ℝ) :
    fmt.finiteRoundToEvenOp BasicOp.add a b =
      fmt.finiteRoundToEvenOp BasicOp.add b a := by
  simp [finiteRoundToEvenOp, BasicOp.exact, add_comm]

/-- Problem 2.7 statement 1, multiplication case, at the ordinary finite
round-to-even layer. -/
theorem finiteRoundToEvenOp_mul_comm
    (fmt : FloatingPointFormat) (a b : ℝ) :
    fmt.finiteRoundToEvenOp BasicOp.mul a b =
      fmt.finiteRoundToEvenOp BasicOp.mul b a := by
  simp [finiteRoundToEvenOp, BasicOp.exact, mul_comm]

/-- Problem 2.7 statement 2 on the exact-representable subtraction branch:
if `a-b` is a finite floating-point value, then both finite round-to-even
subtractions return exact opposite results.  The total selector-level
sign-symmetry theorem below packages this branch with the finite-normal and
off-finite-normal branches under the binary/IEEE-style side conditions. -/
theorem problem2_7_statement2_sub_sign_symmetry_of_exact_finiteSystem
    {fmt : FloatingPointFormat} {a b : ℝ}
    (hab : fmt.finiteSystem (a - b)) :
    fmt.finiteRoundToEvenOp BasicOp.sub b a =
      -fmt.finiteRoundToEvenOp BasicOp.sub a b := by
  have hba : fmt.finiteSystem (b - a) := by
    have hneg := fmt.finiteSystem_neg hab
    convert hneg using 1
    ring
  have hleft :
      fmt.finiteRoundToEvenOp BasicOp.sub b a = b - a := by
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub) (x := b) (y := a) hba)
  have hright :
      fmt.finiteRoundToEvenOp BasicOp.sub a b = a - b := by
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub) (x := a) (y := b) hab)
  rw [hleft, hright]
  ring

/-- Problem 2.7 statement 2 away from the finite-normal branch: the total
finite selector is already sign-symmetric on underflow and overflow exact
subtraction results.  The finite-normal round-to-even choice is handled by the
source-evidence sign-symmetry theorem used in the total wrapper below. -/
theorem problem2_7_statement2_sub_sign_symmetry_of_not_finiteNormalRange
    {fmt : FloatingPointFormat} {a b : ℝ}
    (hab : ¬ fmt.finiteNormalRange (a - b)) :
    fmt.finiteRoundToEvenOp BasicOp.sub b a =
      -fmt.finiteRoundToEvenOp BasicOp.sub a b := by
  simp [finiteRoundToEvenOp, BasicOp.exact]
  rw [show b - a = -(a - b) by ring]
  exact fmt.finiteRoundToEven_neg_of_not_finiteNormalRange hab

/-- Problem 2.7 statement 2 at the finite round-to-even selector layer, for
binary/IEEE-style formats where the radix is even and there is more than one
mantissa digit.  This closes the finite-normal source-selector branch by
source-evidence sign symmetry; full IEEE exception/special-value semantics
remain separate. -/
theorem problem2_7_statement2_sub_sign_symmetry
    {fmt : FloatingPointFormat}
    (hbeta : evenMantissa fmt.beta) (ht : 1 < fmt.t)
    (a b : ℝ) :
    fmt.finiteRoundToEvenOp BasicOp.sub b a =
      -fmt.finiteRoundToEvenOp BasicOp.sub a b := by
  simp [finiteRoundToEvenOp, BasicOp.exact]
  rw [show b - a = -(a - b) by ring]
  exact fmt.finiteRoundToEven_neg hbeta ht (a - b)

/-- Problem 2.7 statement 3 at the ordinary finite round-to-even layer:
rounding `a+a` is the same as rounding `2*a`. -/
theorem finiteRoundToEvenOp_add_self_eq_mul_two
    (fmt : FloatingPointFormat) (a : ℝ) :
    fmt.finiteRoundToEvenOp BasicOp.add a a =
      fmt.finiteRoundToEvenOp BasicOp.mul 2 a := by
  simp [finiteRoundToEvenOp, BasicOp.exact, two_mul]

/-- Problem 2.7 statement 4 at the ordinary finite round-to-even layer:
rounding `(1/2)*a` is the same as rounding `a/2`. -/
theorem finiteRoundToEvenOp_half_mul_eq_div_two
    (fmt : FloatingPointFormat) (a : ℝ) :
  fmt.finiteRoundToEvenOp BasicOp.mul (1 / 2 : ℝ) a =
      fmt.finiteRoundToEvenOp BasicOp.div a 2 := by
  simp [finiteRoundToEvenOp, BasicOp.exact]
  ring_nf

/-- Problem 2.7 statement 5 is false already for finite round-to-even
addition: rounded addition is not associative. -/
theorem problem2_7_statement5_add_associativity_false :
    ¬ (∀ a b c : ℝ,
      decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp BasicOp.add
          (decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
            BasicOp.add a b) c =
        decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp BasicOp.add
          a
          (decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
            BasicOp.add b c)) := by
  intro h
  exact
    decimalOneDigitTwoExponent_roundToEven_add_nonassociative
      (h (10 : ℝ) 4 (-4))

/-- Problem 2.7 statement 6 is false already for finite round-to-even
midpoint rounding: `1 < fl((1+2)/2) < 2` fails in the one-digit decimal
format. -/
theorem problem2_7_statement6_midpoint_strict_between_false :
    ¬ (∀ a b : ℝ,
      decimalOneDigitTwoExponentFormat.finiteSystem a →
        decimalOneDigitTwoExponentFormat.finiteSystem b →
          a < b →
            a <
              decimalOneDigitTwoExponentFormat.finiteRoundToEven
                ((a + b) / 2) ∧
              decimalOneDigitTwoExponentFormat.finiteRoundToEven
                ((a + b) / 2) < b) := by
  intro h
  rcases problem2_8_decimal_midpoint_strict_between_violated with
    ⟨ha, hb, hab, hnot⟩
  exact hnot (h (1 : ℝ) 2 ha hb hab)

end FloatingPointFormat

end

end NumStability
