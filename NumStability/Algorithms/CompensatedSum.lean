-- Algorithms/CompensatedSum.lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Error
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Algorithms.RecursiveSum

namespace NumStability

/-!
# Kahan Compensated Summation (Higham Chapter 4, Algorithm 4.2)

This file records the source-level rounded trace for Higham's compensated
summation loop:

```
s = 0; e = 0
for i = 1:n
  temp = s
  y = x_i + e
  s = temp + y
  e = (temp - s) + y
end
```

The assignment to `e` is represented in the displayed evaluation order.  The
Knuth/Kahan backward and forward error bounds (Higham equations (4.8)--(4.9))
remain separate proof targets.

The p. 93 final-correction variant appends `s = s + e` to Algorithm 4.2; this
file records that final rounded add as a separate returned value.

It also records the source-level correction formula trace behind equation
(4.7): first form `s = fl(a + b)`, then compute `e = fl((a - s) + b)` in the
displayed parenthesized order.  The binary exactness theorem
`a + b = s + e` remains a finite-format proof target.

The same file also records Kahan's no-guard-digit modified correction from
Higham p. 94:

```
f = 0
if sign(temp) = sign(y), f = (0.46 * s - s) + s, end
e = ((temp - f) - (s - f)) + y
```

Finally, it records the p. 94 alternative compensated-summation trace in which
local corrections are accumulated separately by recursive summation before the
global correction is added to the computed sum.
-/

/-- Persistent state of Kahan compensated summation: the current sum `s` and
the correction `e`. -/
structure KahanState where
  s : ℝ
  e : ℝ

namespace KahanState

/-- Initial state `s = 0; e = 0`. -/
def zero : KahanState :=
  { s := 0, e := 0 }

/-- Extensionality for Kahan stored-sum/correction states. -/
@[ext]
theorem ext_state {a b : KahanState} (hs : a.s = b.s) (he : a.e = b.e) :
    a = b := by
  cases a
  cases b
  simp at hs he
  simp [hs, he]

/-- Componentwise addition of stored-sum/correction states. -/
def add (a b : KahanState) : KahanState :=
  { s := a.s + b.s, e := a.e + b.e }

/-- Scalar multiplication of stored-sum/correction states. -/
def smul (c : ℝ) (a : KahanState) : KahanState :=
  { s := c * a.s, e := c * a.e }

/-- Reinterpret a stored-sum/correction pair as the paired
`(compensated total, retained correction)` coordinates used by the
Goldberg-style coefficient recursion. -/
def totalCorrection (a : KahanState) : KahanState :=
  { s := a.s + a.e, e := a.e }

/-- Recover the stored-sum coordinate from a paired
`(compensated total, retained correction)` coefficient state. -/
def returnedFromTotalCorrection (a : KahanState) : ℝ :=
  a.s - a.e

/-- Changing to `(s+e,e)` coordinates and then recovering the returned
stored-sum coordinate gives the original stored sum. -/
theorem returnedFromTotalCorrection_totalCorrection (a : KahanState) :
    returnedFromTotalCorrection (totalCorrection a) = a.s := by
  dsimp [returnedFromTotalCorrection, totalCorrection]
  ring

end KahanState

/-! ## Error-correction formula trace -/

/-- Source-level trace for Higham equation (4.7)'s local correction formula:
`s = fl(a + b)` and `e = fl((a - s) + b)`. -/
structure CorrectionFormulaTrace where
  s : ℝ
  e : ℝ

/-- Predicate for the exactness conclusion of Higham equation (4.7).  The
finite base-2 theorem proving this predicate under the source assumptions is
tracked separately in the Chapter 4 ledger. -/
def CorrectionFormulaTrace.exact (a b : ℝ) (t : CorrectionFormulaTrace) : Prop :=
  a + b = t.s + t.e

/-- The rounded local correction-formula trace. -/
noncomputable def correctionFormulaTrace
    (fp : FPModel) (a b : ℝ) : CorrectionFormulaTrace :=
  let s := fp.fl_add a b
  let e := fp.fl_add (fp.fl_sub a s) b
  { s := s, e := e }

/-- The `s = fl(a + b)` assignment in the correction formula. -/
theorem correctionFormulaTrace_s (fp : FPModel) (a b : ℝ) :
    (correctionFormulaTrace fp a b).s = fp.fl_add a b := by
  rfl

/-- The `e = fl((a - s) + b)` assignment in the correction formula, in the
displayed evaluation order. -/
theorem correctionFormulaTrace_e (fp : FPModel) (a b : ℝ) :
    (correctionFormulaTrace fp a b).e =
      fp.fl_add (fp.fl_sub a (correctionFormulaTrace fp a b).s) b := by
  rfl

/-! ### Finite round-to-even bridge for equation (4.7) -/

/-- Concrete finite round-to-even trace for Higham equation (4.7):
`s = round(a+b)` and `e = round(round(a-s)+b)`. -/
noncomputable def finiteCorrectionFormulaTrace
    (fmt : FloatingPointFormat) (a b : ℝ) : CorrectionFormulaTrace :=
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  let e := fmt.finiteRoundToEvenOp BasicOp.add
    (fmt.finiteRoundToEvenOp BasicOp.sub a s) b
  { s := s, e := e }

/-- The rounded `s = fl(a+b)` assignment for the finite round-to-even trace. -/
theorem finiteCorrectionFormulaTrace_s
    (fmt : FloatingPointFormat) (a b : ℝ) :
    (finiteCorrectionFormulaTrace fmt a b).s =
      fmt.finiteRoundToEvenOp BasicOp.add a b := by
  rfl

/-- The rounded `e = fl((a-s)+b)` assignment for the finite round-to-even trace. -/
theorem finiteCorrectionFormulaTrace_e
    (fmt : FloatingPointFormat) (a b : ℝ) :
    (finiteCorrectionFormulaTrace fmt a b).e =
      fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.finiteRoundToEvenOp BasicOp.sub a
          (finiteCorrectionFormulaTrace fmt a b).s) b := by
  rfl

/-- If the intermediate subtraction `a-s` and the final addition `(a-s)+b`
are exact in the concrete finite round-to-even format, then Higham equation
(4.7)'s exactness conclusion holds. -/
theorem finiteCorrectionFormulaTrace_exact_of_exact_sub_and_finite_error_add
    (fmt : FloatingPointFormat) (a b : ℝ)
    (hsub :
      fmt.finiteRoundToEvenOp BasicOp.sub a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) =
        a - fmt.finiteRoundToEvenOp BasicOp.add a b)
    (hadd :
      fmt.finiteSystem
        ((a - fmt.finiteRoundToEvenOp BasicOp.add a b) + b)) :
    CorrectionFormulaTrace.exact a b
      (finiteCorrectionFormulaTrace fmt a b) := by
  dsimp [CorrectionFormulaTrace.exact, finiteCorrectionFormulaTrace]
  rw [hsub]
  have hadd_exact :
      fmt.finiteRoundToEvenOp BasicOp.add
          (a - fmt.finiteRoundToEvenOp BasicOp.add a b) b =
        (a - fmt.finiteRoundToEvenOp BasicOp.add a b) + b := by
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.add)
        (x := a - fmt.finiteRoundToEvenOp BasicOp.add a b)
        (y := b) hadd)
  rw [hadd_exact]
  ring

/-- Finite-format Sterbenz bridge for Higham equation (4.7).

If `a` and the rounded sum `s = round(a+b)` are finite representable, satisfy
the positive Sterbenz ratio condition, and the final exact error term
`(a-s)+b` is finite representable, then the finite round-to-even correction
trace satisfies `a+b = s+e`.  This is an intermediate finite-format route to
the full Dekker/Knuth/Linnainmaa base-2 theorem, not yet the full all-signs
FastTwoSum result. -/
theorem finiteCorrectionFormulaTrace_exact_of_sterbenz_and_finite_error_add
    (fmt : FloatingPointFormat) (a b : ℝ)
    (ha : fmt.finiteSystem a)
    (hs : fmt.finiteSystem (fmt.finiteRoundToEvenOp BasicOp.add a b))
    (hsterbenz :
      fmt.sterbenzRatioCondition a
        (fmt.finiteRoundToEvenOp BasicOp.add a b))
    (hadd :
      fmt.finiteSystem
        ((a - fmt.finiteRoundToEvenOp BasicOp.add a b) + b)) :
    CorrectionFormulaTrace.exact a b
      (finiteCorrectionFormulaTrace fmt a b) := by
  have hsub :
      fmt.finiteRoundToEvenOp BasicOp.sub a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) =
        a - fmt.finiteRoundToEvenOp BasicOp.add a b :=
    fmt.finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioCondition
      ha hs hsterbenz
  exact finiteCorrectionFormulaTrace_exact_of_exact_sub_and_finite_error_add
    fmt a b hsub hadd

/-- Signed finite-format Sterbenz bridge for Higham equation (4.7).

This extends `finiteCorrectionFormulaTrace_exact_of_sterbenz_and_finite_error_add`
from the positive Sterbenz branch to the same-sign negative branch: if either
`a` and `s = round(a+b)` satisfy the positive Sterbenz ratio condition, or
their sign-flipped values `-a` and `-s` do, then the intermediate subtraction
`a-s` is finite representable and therefore rounded exactly.  The final
error-add representability assumption is still explicit; deriving it from the
printed Dekker/Knuth/Linnainmaa hypotheses remains the full FastTwoSum proof
target. -/
theorem finiteCorrectionFormulaTrace_exact_of_signed_sterbenz_and_finite_error_add
    (fmt : FloatingPointFormat) (a b : ℝ)
    (ha : fmt.finiteSystem a)
    (hs : fmt.finiteSystem (fmt.finiteRoundToEvenOp BasicOp.add a b))
    (hsterbenz :
      fmt.sterbenzRatioCondition a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) ∨
        fmt.sterbenzRatioCondition (-a)
          (-(fmt.finiteRoundToEvenOp BasicOp.add a b)))
    (hadd :
      fmt.finiteSystem
        ((a - fmt.finiteRoundToEvenOp BasicOp.add a b) + b)) :
    CorrectionFormulaTrace.exact a b
      (finiteCorrectionFormulaTrace fmt a b) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hs' : fmt.finiteSystem s := by
    simpa [s] using hs
  have hsub_finite : fmt.finiteSystem (a - s) := by
    rcases hsterbenz with hpos | hneg
    · exact
        fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
          (x := a) (y := s) ha hs' (by simpa [s] using hpos)
    · have hneg_a : fmt.finiteSystem (-a) := fmt.finiteSystem_neg ha
      have hneg_s : fmt.finiteSystem (-s) := fmt.finiteSystem_neg hs'
      have hfin_neg :
          fmt.finiteSystem ((-a) - (-s)) :=
        fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
          (x := -a) (y := -s) hneg_a hneg_s (by simpa [s] using hneg)
      have hrewrite : a - s = -((-a) - (-s)) := by ring
      rw [hrewrite]
      exact fmt.finiteSystem_neg hfin_neg
  have hsub :
      fmt.finiteRoundToEvenOp BasicOp.sub a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) =
        a - fmt.finiteRoundToEvenOp BasicOp.add a b := by
    have hsub_finite' :
        fmt.finiteSystem
          (BasicOp.exact BasicOp.sub a
            (fmt.finiteRoundToEvenOp BasicOp.add a b)) := by
      simpa [BasicOp.exact, s] using hsub_finite
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub) (x := a)
        (y := fmt.finiteRoundToEvenOp BasicOp.add a b) hsub_finite')
  exact finiteCorrectionFormulaTrace_exact_of_exact_sub_and_finite_error_add
    fmt a b hsub hadd

/-- Two-stage signed finite-format Sterbenz bridge for Higham equation (4.7).

The first signed Sterbenz condition proves that the intermediate subtraction
`a-s` is exact.  The second signed Sterbenz condition proves that the final
exact error term is finite representable via
`(a-s)+b = (a+b)-s`, so the final rounded add is exact as well.  This removes
the explicit final-add finite-system assumption from
`finiteCorrectionFormulaTrace_exact_of_signed_sterbenz_and_finite_error_add`,
but still leaves the source-level task of deriving these certificates from the
printed FastTwoSum hypotheses. -/
theorem finiteCorrectionFormulaTrace_exact_of_two_signed_sterbenz
    (fmt : FloatingPointFormat) (a b : ℝ)
    (ha : fmt.finiteSystem a)
    (hs : fmt.finiteSystem (fmt.finiteRoundToEvenOp BasicOp.add a b))
    (hexact : fmt.finiteSystem (a + b))
    (hsub_sterbenz :
      fmt.sterbenzRatioCondition a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) ∨
        fmt.sterbenzRatioCondition (-a)
          (-(fmt.finiteRoundToEvenOp BasicOp.add a b)))
    (herr_sterbenz :
      fmt.sterbenzRatioCondition (a + b)
          (fmt.finiteRoundToEvenOp BasicOp.add a b) ∨
        fmt.sterbenzRatioCondition (-(a + b))
          (-(fmt.finiteRoundToEvenOp BasicOp.add a b))) :
    CorrectionFormulaTrace.exact a b
      (finiteCorrectionFormulaTrace fmt a b) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hs' : fmt.finiteSystem s := by
    simpa [s] using hs
  have herror_finite : fmt.finiteSystem ((a + b) - s) := by
    rcases herr_sterbenz with hpos | hneg
    · exact
        fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
          (x := a + b) (y := s) hexact hs' (by simpa [s] using hpos)
    · have hneg_exact : fmt.finiteSystem (-(a + b)) :=
        fmt.finiteSystem_neg hexact
      have hneg_s : fmt.finiteSystem (-s) := fmt.finiteSystem_neg hs'
      have hfin_neg :
          fmt.finiteSystem (-(a + b) - (-s)) :=
        fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
          (x := -(a + b)) (y := -s) hneg_exact hneg_s
          (by simpa [s] using hneg)
      have hrewrite : (a + b) - s = -( -(a + b) - (-s)) := by ring
      rw [hrewrite]
      exact fmt.finiteSystem_neg hfin_neg
  have hadd :
      fmt.finiteSystem
        ((a - fmt.finiteRoundToEvenOp BasicOp.add a b) + b) := by
    have hrewrite :
        (a - s) + b = (a + b) - s := by ring
    simpa [s, hrewrite] using herror_finite
  exact finiteCorrectionFormulaTrace_exact_of_signed_sterbenz_and_finite_error_add
    fmt a b ha hs hsub_sterbenz hadd

/-- Representability certificate for the finite FastTwoSum/correction-formula
bridge behind Higham equation (4.7).

This is not the full Dekker/Knuth/Linnainmaa theorem: it records the exact
finite-format obligations that the all-signs base-2 proof must derive from
the printed assumptions. -/
structure FastTwoSumFiniteCertificate
    (fmt : FloatingPointFormat) (a b : ℝ) : Prop where
  /-- The rounded sum produced by the first operation. -/
  finite_s : fmt.finiteSystem (fmt.finiteRoundToEvenOp BasicOp.add a b)
  /-- The intermediate subtraction `a - s` is representable, so it rounds
  exactly. -/
  finite_a_sub_s :
    fmt.finiteSystem (a - fmt.finiteRoundToEvenOp BasicOp.add a b)
  /-- The true local error `(a+b)-s` is representable, so the final error add
  can round exactly. -/
  finite_error :
    fmt.finiteSystem ((a + b) - fmt.finiteRoundToEvenOp BasicOp.add a b)

/-- The first rounded addition in the finite real-valued selector always
returns a finite-format value.  Future FastTwoSum proofs therefore need not
carry `s`-finite as a source hypothesis; only the two local-error
representability obligations are genuine. -/
theorem FastTwoSumFiniteCertificate.finite_s_unconditional
    (fmt : FloatingPointFormat) (a b : ℝ) :
    fmt.finiteSystem (fmt.finiteRoundToEvenOp BasicOp.add a b) :=
  fmt.finiteRoundToEvenOp_finiteSystem BasicOp.add a b

/-- Build the finite FastTwoSum certificate from exactly the two nontrivial
representability obligations: `a-s` and the true local error `(a+b)-s`. -/
theorem FastTwoSumFiniteCertificate.of_error_obligations
    (fmt : FloatingPointFormat) (a b : ℝ)
    (hsub :
      fmt.finiteSystem (a - fmt.finiteRoundToEvenOp BasicOp.add a b))
    (herr :
      fmt.finiteSystem ((a + b) - fmt.finiteRoundToEvenOp BasicOp.add a b)) :
    FastTwoSumFiniteCertificate fmt a b :=
  { finite_s := FastTwoSumFiniteCertificate.finite_s_unconditional fmt a b
    finite_a_sub_s := hsub
    finite_error := herr }

/-- Same-lattice coefficient bridge for the true FastTwoSum local error.

If the exact source `a+b` and rounded endpoint `s = fl(a+b)` have already
been placed on the same signed scaled-integer exponent lattice, and their
integer coefficient gap has fewer than `t` radix digits, then the true local
error `(a+b)-s` is finite representable.  This is the direct certificate-field
handoff needed by the remaining finite binary operand-grid proof. -/
theorem FastTwoSumFiniteCertificate.finite_error_of_sameExponentScaledInteger
    (fmt : FloatingPointFormat) (a b : ℝ)
    {negative : Bool} {k l : ℤ} {e : ℤ}
    (hsource :
      a + b =
        fmt.signValue negative * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)))
    (hround :
      fmt.finiteRoundToEvenOp BasicOp.add a b =
        fmt.signValue negative * (l : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)))
    (he : fmt.exponentInRange e)
    (hdiff : (k - l).natAbs < fmt.beta ^ fmt.t) :
    fmt.finiteSystem ((a + b) - fmt.finiteRoundToEvenOp BasicOp.add a b) := by
  rw [hsource, hround]
  exact
    fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := negative) (k := k) (l := l) (e := e) he hdiff

/-- The current finite-format two-Sterbenz route packaged as a
`FastTwoSumFiniteCertificate`.

The first signed Sterbenz certificate proves representability of `a-s`; the
second proves representability of the true local error `(a+b)-s`.  The
remaining C4.4 source-level gap is deriving these signed Sterbenz certificates
from the printed base-2 `|a| > |b|` hypotheses. -/
theorem FastTwoSumFiniteCertificate.of_two_signed_sterbenz
    (fmt : FloatingPointFormat) (a b : ℝ)
    (ha : fmt.finiteSystem a)
    (hs : fmt.finiteSystem (fmt.finiteRoundToEvenOp BasicOp.add a b))
    (hexact : fmt.finiteSystem (a + b))
    (hsub_sterbenz :
      fmt.sterbenzRatioCondition a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) ∨
        fmt.sterbenzRatioCondition (-a)
          (-(fmt.finiteRoundToEvenOp BasicOp.add a b)))
    (herr_sterbenz :
      fmt.sterbenzRatioCondition (a + b)
          (fmt.finiteRoundToEvenOp BasicOp.add a b) ∨
        fmt.sterbenzRatioCondition (-(a + b))
          (-(fmt.finiteRoundToEvenOp BasicOp.add a b))) :
    FastTwoSumFiniteCertificate fmt a b := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hs' : fmt.finiteSystem s := by
    simpa [s] using hs
  refine
    { finite_s := hs
      finite_a_sub_s := ?_
      finite_error := ?_ }
  · have hsub_finite : fmt.finiteSystem (a - s) := by
      rcases hsub_sterbenz with hpos | hneg
      · exact
          fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
            (x := a) (y := s) ha hs' (by simpa [s] using hpos)
      · have hneg_a : fmt.finiteSystem (-a) := fmt.finiteSystem_neg ha
        have hneg_s : fmt.finiteSystem (-s) := fmt.finiteSystem_neg hs'
        have hfin_neg :
            fmt.finiteSystem ((-a) - (-s)) :=
          fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
            (x := -a) (y := -s) hneg_a hneg_s (by simpa [s] using hneg)
        have hrewrite : a - s = -((-a) - (-s)) := by ring
        rw [hrewrite]
        exact fmt.finiteSystem_neg hfin_neg
    simpa [s] using hsub_finite
  · have herror_finite : fmt.finiteSystem ((a + b) - s) := by
      rcases herr_sterbenz with hpos | hneg
      · exact
          fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
            (x := a + b) (y := s) hexact hs' (by simpa [s] using hpos)
      · have hneg_exact : fmt.finiteSystem (-(a + b)) :=
          fmt.finiteSystem_neg hexact
        have hneg_s : fmt.finiteSystem (-s) := fmt.finiteSystem_neg hs'
        have hfin_neg :
            fmt.finiteSystem (-(a + b) - (-s)) :=
          fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
            (x := -(a + b)) (y := -s) hneg_exact hneg_s
            (by simpa [s] using hneg)
        have hrewrite : (a + b) - s = -( -(a + b) - (-s)) := by ring
        rw [hrewrite]
        exact fmt.finiteSystem_neg hfin_neg
    simpa [s] using herror_finite

/-- The source magnitude condition `|b| < |a|` does not by itself imply the
signed Sterbenz certificate between `a` and the exact sum `a+b`.

The cancellation pair `a = 1`, `b = -3/4` has `|b| < |a|` and positive exact
sum `1/4`, but neither the positive nor sign-flipped Sterbenz ratio condition
holds between `a` and `a+b`.  Thus the full base-2 proof of Higham equation
(4.7) needs a real FastTwoSum/Dekker-Knuth split, not just the source
magnitude hypothesis plus the existing Sterbenz bridge. -/
theorem correctionFormula_abs_order_not_imply_signed_sterbenz_exact_sum
    (fmt : FloatingPointFormat) :
    ∃ a b : ℝ,
      |b| < |a| ∧ 0 < a + b ∧
        ¬ (fmt.sterbenzRatioCondition a (a + b) ∨
          fmt.sterbenzRatioCondition (-a) (-(a + b))) := by
  refine ⟨1, (-3 / 4 : ℝ), ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · unfold FloatingPointFormat.sterbenzRatioCondition
    norm_num

/-- A tiny binary format used to test the endpoint of the strict Sterbenz
route for the C4.4/FastTwoSum proof.

With base `2` and precision `t = 2`, the exact value `1 + 3/4 = 7/4` is the
tie between `3/2` and `2`; round-to-even selects `2` because the left endpoint
has odd mantissa `3`. -/
def correctionFormulaStrictSterbenzEndpointFormat : FloatingPointFormat where
  beta := 2
  t := 2
  emin := 0
  emax := 2
  beta_ge_two := by norm_num
  t_pos := by norm_num
  emin_le_emax := by norm_num

/-- Endpoint computation for the strict-Sterbenz route counterexample.

In the two-digit binary format above, `fl(1 + 3/4) = 2`.  This is an inexact
first addition satisfying the printed `|b| < |a|` order, but the rounded sum is
exactly `2*a`, so the local strict Sterbenz predicate between `a` and `s`
cannot hold. -/
theorem correctionFormulaStrictSterbenzEndpoint_round_one_add_three_quarters :
    correctionFormulaStrictSterbenzEndpointFormat.finiteRoundToEvenOp
      BasicOp.add (1 : ℝ) (3 / 4 : ℝ) = (2 : ℝ) := by
  let fmt := correctionFormulaStrictSterbenzEndpointFormat
  let left : ℝ := fmt.normalizedValue false fmt.maxNormalMantissa (1 : ℤ)
  let right : ℝ := fmt.normalizedValue false fmt.minNormalMantissa (2 : ℤ)
  let x : ℝ := (7 / 4 : ℝ)
  have hm : fmt.normalizedMantissa fmt.maxNormalMantissa :=
    fmt.maxNormalMantissa_normalized
  have hboundary : fmt.boundaryAdjacentNormalized left right := by
    exact ⟨false, (1 : ℤ), Or.inl ⟨rfl, rfl⟩⟩
  have hadj : fmt.realOrderAdjacentNormalized left right :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have hleft_value : left = (3 / 2 : ℝ) := by
    norm_num [left, fmt, correctionFormulaStrictSterbenzEndpointFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.minNormalMantissa, zpow_neg]
  have hright_value : right = (2 : ℝ) := by
    norm_num [right, fmt, correctionFormulaStrictSterbenzEndpointFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.minNormalMantissa, zpow_neg]
  have hstrict : left < x ∧ x < right := by
    rw [hleft_value, hright_value]
    norm_num [x]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by norm_num [x]
    rw [abs_of_nonneg hxnonneg]
    constructor
    · norm_num [x, fmt, correctionFormulaStrictSterbenzEndpointFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
    · norm_num [x, fmt, correctionFormulaStrictSterbenzEndpointFormat,
        FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
      exact (le_of_not_gt (by norm_num : ¬ (3 : ℝ) < 7 / 4))
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hxrange
  have hleft_repr :
      left = fmt.normalizedValue false fmt.maxNormalMantissa (1 : ℤ) := rfl
  have htie : |x - left| = |x - right| := by
    rw [hleft_value, hright_value]
    norm_num [x]
  have hodd : ¬ FloatingPointFormat.evenMantissa fmt.maxNormalMantissa := by
    norm_num [fmt, correctionFormulaStrictSterbenzEndpointFormat,
      FloatingPointFormat.maxNormalMantissa, FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven x = right :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hm hleft_repr htie hodd
  change fmt.finiteRoundToEven
      (BasicOp.exact BasicOp.add (1 : ℝ) (3 / 4 : ℝ)) =
    (2 : ℝ)
  have hxop : BasicOp.exact BasicOp.add (1 : ℝ) (3 / 4 : ℝ) = x := by
    norm_num [BasicOp.exact, x]
  rw [hxop]
  simpa [fmt, hright_value] using hround

/-- The strict signed-Sterbenz line-2 condition is not implied by the printed
base-2 FastTwoSum hypotheses plus an inexact first addition.

This rules out the previous C4.4 bottleneck subtarget as stated.  The endpoint
case has finite binary operands, `|b| < |a|`, finite-normal exact sum, and an
inexact rounded first add, but `fl(a+b) = 2*a`, so the local strict
`sterbenzRatioCondition` fails in both sign orientations.  A complete
FastTwoSum proof must therefore use a corrected line-2 dependency, for example
an inclusive Sterbenz endpoint branch or a direct representability theorem for
`a - fl(a+b)`. -/
theorem correctionFormula_base2_abs_gt_inexact_not_imply_signed_sterbenz :
    ∃ fmt : FloatingPointFormat, ∃ a b : ℝ,
      fmt.beta = 2 ∧ 1 < fmt.t ∧
        fmt.finiteSystem a ∧ fmt.finiteSystem b ∧
        |b| < |a| ∧ fmt.finiteNormalRange (a + b) ∧
        fmt.finiteRoundToEvenOp BasicOp.add a b ≠ a + b ∧
        ¬ (fmt.sterbenzRatioCondition a
              (fmt.finiteRoundToEvenOp BasicOp.add a b) ∨
            fmt.sterbenzRatioCondition (-a)
              (-(fmt.finiteRoundToEvenOp BasicOp.add a b))) := by
  refine
    ⟨correctionFormulaStrictSterbenzEndpointFormat,
      (1 : ℝ), (3 / 4 : ℝ), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [correctionFormulaStrictSterbenzEndpointFormat]
  · norm_num [correctionFormulaStrictSterbenzEndpointFormat]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 2, (1 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        correctionFormulaStrictSterbenzEndpointFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        correctionFormulaStrictSterbenzEndpointFormat]
    · norm_num [FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue, FloatingPointFormat.betaR,
        correctionFormulaStrictSterbenzEndpointFormat, zpow_neg]
      rfl
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 3, (0 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        correctionFormulaStrictSterbenzEndpointFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        correctionFormulaStrictSterbenzEndpointFormat]
    · norm_num [FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue, FloatingPointFormat.betaR,
        correctionFormulaStrictSterbenzEndpointFormat, zpow_neg]
  · norm_num
  · rw [FloatingPointFormat.finiteNormalRange]
    norm_num [FloatingPointFormat.minNormalMagnitude,
      FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
      correctionFormulaStrictSterbenzEndpointFormat, zpow_neg]
    exact (le_of_not_gt (by norm_num : ¬ (3 : ℝ) < 7 / 4))
  · rw [correctionFormulaStrictSterbenzEndpoint_round_one_add_three_quarters]
    norm_num
  · rw [correctionFormulaStrictSterbenzEndpoint_round_one_add_three_quarters]
    unfold FloatingPointFormat.sterbenzRatioCondition
    norm_num

/-- Exact-first-add branch for the finite FastTwoSum/correction-formula
certificate.

If the first rounded addition already returns the exact real sum, then the
intermediate subtraction is `-b` and the true local error is zero.  This closes
one concrete split case of the full base-2 proof of Higham equation (4.7). -/
theorem FastTwoSumFiniteCertificate.of_exact_add
    (fmt : FloatingPointFormat) (a b : ℝ)
    (hb : fmt.finiteSystem b)
    (hadd :
      fmt.finiteRoundToEvenOp BasicOp.add a b = a + b) :
    FastTwoSumFiniteCertificate fmt a b := by
  refine
    { finite_s := fmt.finiteRoundToEvenOp_finiteSystem BasicOp.add a b
      finite_a_sub_s := ?_
      finite_error := ?_ }
  · have hrewrite :
        a - fmt.finiteRoundToEvenOp BasicOp.add a b = -b := by
      rw [hadd]
      ring
    rw [hrewrite]
    exact fmt.finiteSystem_neg hb
  · have hrewrite :
        (a + b) - fmt.finiteRoundToEvenOp BasicOp.add a b = 0 := by
      rw [hadd]
      ring
    rw [hrewrite]
    exact Or.inl rfl

/-- Base-2 absolute-order FastTwoSum certificate once the remaining
intermediate-subtraction representability field is supplied.

The rounded-add local-error field is no longer a C4.4 obstruction: under the
source finite binary operand hypotheses and finite-normal-range condition it
follows from
`finiteRoundToEvenOp_add_error_finite_of_base2_abs_order_of_finiteNormalRange`.
The remaining source-level FastTwoSum/Dekker-Knuth step is exactly the
representability of `a - fl(a+b)`. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_order_of_finite_a_sub_s
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hsub :
      fmt.finiteSystem (a - fmt.finiteRoundToEvenOp BasicOp.add a b)) :
    FastTwoSumFiniteCertificate fmt a b :=
  FastTwoSumFiniteCertificate.of_error_obligations fmt a b hsub
    (fmt.finiteRoundToEvenOp_add_error_finite_of_base2_abs_order_of_finiteNormalRange
      hbeta ht ha hb hab habRange)

/-- Signed Sterbenz line-2 branch for the finite FastTwoSum certificate.

If `a` and the rounded first sum `s = fl(a+b)` satisfy Sterbenz after a
possible simultaneous sign flip, then the intermediate subtraction `a-s` is
finite representable. -/
theorem FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz
    (fmt : FloatingPointFormat) {a b : ℝ}
    (ha : fmt.finiteSystem a)
    (hsub_sterbenz :
      fmt.sterbenzRatioCondition a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) ∨
        fmt.sterbenzRatioCondition (-a)
          (-(fmt.finiteRoundToEvenOp BasicOp.add a b))) :
    fmt.finiteSystem
      (a - fmt.finiteRoundToEvenOp BasicOp.add a b) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hs : fmt.finiteSystem s :=
    FastTwoSumFiniteCertificate.finite_s_unconditional fmt a b
  have hsub : fmt.finiteSystem (a - s) := by
    rcases hsub_sterbenz with hpos | hneg
    · exact
        fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
          (x := a) (y := s) ha hs (by simpa [s] using hpos)
    · have hneg_a : fmt.finiteSystem (-a) := fmt.finiteSystem_neg ha
      have hneg_s : fmt.finiteSystem (-s) := fmt.finiteSystem_neg hs
      have hfin_neg :
          fmt.finiteSystem ((-a) - (-s)) :=
        fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
          (x := -a) (y := -s) hneg_a hneg_s (by simpa [s] using hneg)
      have hrewrite : a - s = -((-a) - (-s)) := by ring
      rw [hrewrite]
      exact fmt.finiteSystem_neg hfin_neg
  simpa [s] using hsub

/-- Endpoint-inclusive line-2 branch for the finite FastTwoSum certificate.

The strict signed-Sterbenz branch proves representability of `a-s` away from
the endpoints.  If strict Sterbenz fails only because `s = 2*a`, then
`a-s = -a`; if it fails because `a = 2*s`, then `a-s = s`.  Both values are
finite representable from the source finite operand and the rounded sum's
unconditional finite-system certificate. -/
theorem FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz_or_endpoint
    (fmt : FloatingPointFormat) {a b : ℝ}
    (ha : fmt.finiteSystem a)
    (hsub :
      (fmt.sterbenzRatioCondition a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) ∨
        fmt.sterbenzRatioCondition (-a)
          (-(fmt.finiteRoundToEvenOp BasicOp.add a b))) ∨
      fmt.finiteRoundToEvenOp BasicOp.add a b = 2 * a ∨
      a = 2 * fmt.finiteRoundToEvenOp BasicOp.add a b) :
    fmt.finiteSystem
      (a - fmt.finiteRoundToEvenOp BasicOp.add a b) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  rcases hsub with hsterbenz | hendpoint
  · exact
      FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz
        fmt ha hsterbenz
  rcases hendpoint with hs_double | ha_double
  · have hs_double' : s = 2 * a := by
      simpa [s] using hs_double
    have hrewrite : a - s = -a := by
      rw [hs_double']
      ring
    rw [hrewrite]
    exact fmt.finiteSystem_neg ha
  · have hs : fmt.finiteSystem s :=
      FastTwoSumFiniteCertificate.finite_s_unconditional fmt a b
    have ha_double' : a = 2 * s := by
      simpa [s] using ha_double
    have hrewrite : a - s = s := by
      rw [ha_double']
      ring
    rw [hrewrite]
    exact hs

/-- Non-strict signed ratio bounds imply the endpoint-inclusive line-2 branch
for the finite FastTwoSum certificate.

This is the next local form needed for the Dekker/Knuth split: if the rounded
first sum `s = fl(a+b)` and `a` satisfy the non-strict Sterbenz bounds after a
possible simultaneous sign flip, then either strict signed Sterbenz holds or
one of the two endpoint equalities `s = 2*a`, `a = 2*s` holds. -/
theorem FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_ratio_bounds
    (fmt : FloatingPointFormat) {a b : ℝ}
    (ha : fmt.finiteSystem a)
    (hbounds :
      let s := fmt.finiteRoundToEvenOp BasicOp.add a b
      (s ≤ 2 * a ∧ a ≤ 2 * s) ∨
      (-s ≤ 2 * (-a) ∧ -a ≤ 2 * (-s))) :
    fmt.finiteSystem
      (a - fmt.finiteRoundToEvenOp BasicOp.add a b) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hbounds' :
      (s ≤ 2 * a ∧ a ≤ 2 * s) ∨
      (-s ≤ 2 * (-a) ∧ -a ≤ 2 * (-s)) := by
    simpa [s] using hbounds
  rcases hbounds' with hpos | hneg
  · rcases hpos with ⟨hs_le, ha_le⟩
    by_cases hs_double : s = 2 * a
    · exact
        FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz_or_endpoint
          fmt ha (Or.inr (Or.inl (by simpa [s] using hs_double)))
    by_cases ha_double : a = 2 * s
    · exact
        FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz_or_endpoint
          fmt ha (Or.inr (Or.inr (by simpa [s] using ha_double)))
    have hs_lt : s < 2 * a := lt_of_le_of_ne hs_le hs_double
    have ha_lt : a < 2 * s := lt_of_le_of_ne ha_le ha_double
    have hsterbenz : fmt.sterbenzRatioCondition a s := by
      unfold FloatingPointFormat.sterbenzRatioCondition
      constructor
      · linarith
      · exact ha_lt
    exact
      FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz_or_endpoint
        fmt ha (Or.inl (Or.inl (by simpa [s] using hsterbenz)))
  · rcases hneg with ⟨hns_le, hna_le⟩
    by_cases hns_double : -s = 2 * (-a)
    · have hs_double : s = 2 * a := by linarith
      exact
        FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz_or_endpoint
          fmt ha (Or.inr (Or.inl (by simpa [s] using hs_double)))
    by_cases hna_double : -a = 2 * (-s)
    · have ha_double : a = 2 * s := by linarith
      exact
        FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz_or_endpoint
          fmt ha (Or.inr (Or.inr (by simpa [s] using ha_double)))
    have hns_lt : -s < 2 * (-a) := lt_of_le_of_ne hns_le hns_double
    have hna_lt : -a < 2 * (-s) := lt_of_le_of_ne hna_le hna_double
    have hsterbenz : fmt.sterbenzRatioCondition (-a) (-s) := by
      unfold FloatingPointFormat.sterbenzRatioCondition
      constructor
      · linarith
      · exact hna_lt
    exact
      FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz_or_endpoint
        fmt ha (Or.inl (Or.inr (by simpa [s] using hsterbenz)))

/-- Positive/negative far-magnitude source split for the signed-ratio
FastTwoSum route.

If the first rounded add is inexact, the already-closed near-magnitude branch
rules out `a < 2*(-b)`.  The exact sum is then bracketed above by the finite
candidate `a` and below either by the finite half `a/2` or, at the bottom
binade, by `minNormalMagnitude`.  The rounded-add interval theorem transfers
that exact-sum bracket to the rounded first sum `s`. -/
theorem FastTwoSumFiniteCertificate.signed_ratio_bounds_of_pos_neg_abs_order_inexact
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (ha_nonneg : 0 ≤ a) (hb_nonpos : b ≤ 0)
    (hinexact : fmt.finiteRoundToEvenOp BasicOp.add a b ≠ a + b) :
    let s := fmt.finiteRoundToEvenOp BasicOp.add a b
    s ≤ 2 * a ∧ a ≤ 2 * s := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hmag : -b < a := by
    simpa [abs_of_nonpos hb_nonpos, abs_of_nonneg ha_nonneg] using hab
  have hnot_lt :
      ¬ a < 2 * (-b) :=
    fmt.finiteRoundToEvenOp_add_pos_neg_finiteSystem_not_lt_two_of_ne_exact
      ha hb ha_nonneg hb_nonpos hinexact hmag
  have hfar : 2 * (-b) ≤ a := le_of_not_gt hnot_lt
  have hsum_lower_half : a / 2 ≤ a + b := by
    nlinarith
  have hsum_le_a : a + b ≤ a := by
    linarith
  have hs_le_a : s ≤ a := by
    simpa [s] using
      fmt.finiteRoundToEvenOp_add_le_of_exact_le_finiteSystem
        ha hsum_le_a
  have hs_le_two_a : s ≤ 2 * a := by
    nlinarith
  have ha_le_two_s : a ≤ 2 * s := by
    rcases
      fmt.finiteSystem_half_or_le_two_minNormalMagnitude_of_nonneg_baseTwo
        hbeta ha ha_nonneg with hhalf_fin | ha_small
    · have hhalf_le_s : a / 2 ≤ s := by
        simpa [s] using
          fmt.finiteRoundToEvenOp_add_ge_of_finiteSystem_le_exact
            hhalf_fin hsum_lower_half
      nlinarith
    · have hsum_pos : 0 < a + b := by
        nlinarith
      have hsum_abs : |a + b| = a + b :=
        abs_of_nonneg (le_of_lt hsum_pos)
      have hmin_le_sum : fmt.minNormalMagnitude ≤ a + b := by
        simpa [hsum_abs] using habRange.1
      have hmin_le_s : fmt.minNormalMagnitude ≤ s := by
        simpa [s] using
          fmt.finiteRoundToEvenOp_add_ge_of_finiteSystem_le_exact
            fmt.minNormalMagnitude_mem_finiteSystem hmin_le_sum
      nlinarith
  exact ⟨hs_le_two_a, ha_le_two_s⟩

/-- Sign-symmetric negative/positive far-magnitude source split for the
signed-ratio FastTwoSum route. -/
theorem FastTwoSumFiniteCertificate.signed_ratio_bounds_of_neg_pos_abs_order_inexact
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (ha_nonpos : a ≤ 0) (hb_nonneg : 0 ≤ b)
    (hinexact : fmt.finiteRoundToEvenOp BasicOp.add a b ≠ a + b) :
    let s := fmt.finiteRoundToEvenOp BasicOp.add a b
    (-s ≤ 2 * (-a) ∧ -a ≤ 2 * (-s)) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  let sp := fmt.finiteRoundToEvenOp BasicOp.add (-a) (-b)
  have hbeta_even : FloatingPointFormat.evenMantissa fmt.beta := by
    unfold FloatingPointFormat.evenMantissa
    omega
  have hs_eq_neg_sp : s = -sp := by
    dsimp [s, sp, FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact]
    have hsum : a + b = -((-a) + (-b)) := by ring
    rw [hsum]
    simpa using
      fmt.finiteRoundToEven_neg hbeta_even ht ((-a) + (-b))
  have hinexact_neg :
      fmt.finiteRoundToEvenOp BasicOp.add (-a) (-b) ≠ (-a) + (-b) := by
    intro hexact_neg
    exact hinexact (by
      change s = a + b
      rw [hs_eq_neg_sp]
      have hsp_exact : sp = (-a) + (-b) := by
        simpa [sp] using hexact_neg
      rw [hsp_exact]
      ring)
  have hneg_range : fmt.finiteNormalRange ((-a) + (-b)) := by
    have h := (fmt.finiteNormalRange_neg_iff (a + b)).mpr habRange
    simpa [add_comm, add_left_comm, add_assoc] using h
  have hpos_bounds :
      sp ≤ 2 * (-a) ∧ -a ≤ 2 * sp := by
    simpa [sp] using
      FastTwoSumFiniteCertificate.signed_ratio_bounds_of_pos_neg_abs_order_inexact
        fmt hbeta
        (a := -a) (b := -b)
        (fmt.finiteSystem_neg ha) (fmt.finiteSystem_neg hb)
        (by simpa [abs_neg] using hab)
        hneg_range
        (by linarith) (by linarith)
        hinexact_neg
  have hneg_s_eq_sp : -s = sp := by
    rw [hs_eq_neg_sp]
    ring
  constructor
  · rw [hneg_s_eq_sp]
    exact hpos_bounds.1
  · rw [hneg_s_eq_sp]
    exact hpos_bounds.2

/-- Opposite-sign inexact source split for the signed-ratio FastTwoSum route. -/
theorem FastTwoSumFiniteCertificate.signed_ratio_bounds_of_opposite_sign_abs_order_inexact
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hsign : (0 ≤ a ∧ b ≤ 0) ∨ (a ≤ 0 ∧ 0 ≤ b))
    (hinexact : fmt.finiteRoundToEvenOp BasicOp.add a b ≠ a + b) :
    let s := fmt.finiteRoundToEvenOp BasicOp.add a b
    (s ≤ 2 * a ∧ a ≤ 2 * s) ∨
      (-s ≤ 2 * (-a) ∧ -a ≤ 2 * (-s)) := by
  rcases hsign with hposneg | hnegpos
  · exact Or.inl
      (by
        simpa using
          FastTwoSumFiniteCertificate.signed_ratio_bounds_of_pos_neg_abs_order_inexact
            fmt hbeta ha hb hab habRange hposneg.1 hposneg.2 hinexact)
  · exact Or.inr
      (by
        simpa using
          FastTwoSumFiniteCertificate.signed_ratio_bounds_of_neg_pos_abs_order_inexact
            fmt hbeta ht ha hb hab habRange hnegpos.1 hnegpos.2 hinexact)

/-- Same-sign absolute ratio bounds imply the signed ratio-bound line-2 branch
for the finite FastTwoSum certificate.

This is a source-facing adapter: once the operand split proves that `a` and the
rounded first sum `s = fl(a+b)` have the same sign, ordinary absolute bounds
`|s| <= 2|a|` and `|a| <= 2|s|` are enough to reuse the signed-ratio
certificate field. -/
theorem FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_abs_ratio_bounds
    (fmt : FloatingPointFormat) {a b : ℝ}
    (ha : fmt.finiteSystem a)
    (hbounds :
      let s := fmt.finiteRoundToEvenOp BasicOp.add a b
      (((0 ≤ a ∧ 0 ≤ s) ∨ (a ≤ 0 ∧ s ≤ 0)) ∧
        |s| ≤ 2 * |a| ∧ |a| ≤ 2 * |s|)) :
    fmt.finiteSystem
      (a - fmt.finiteRoundToEvenOp BasicOp.add a b) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hbounds' :
      ((0 ≤ a ∧ 0 ≤ s) ∨ (a ≤ 0 ∧ s ≤ 0)) ∧
        |s| ≤ 2 * |a| ∧ |a| ≤ 2 * |s| := by
    simpa [s] using hbounds
  rcases hbounds' with ⟨hsign, hs_abs, ha_abs⟩
  have hsigned :
      (s ≤ 2 * a ∧ a ≤ 2 * s) ∨
      (-s ≤ 2 * (-a) ∧ -a ≤ 2 * (-s)) := by
    rcases hsign with hnonneg | hnonpos
    · rcases hnonneg with ⟨ha_nonneg, hs_nonneg⟩
      left
      constructor
      · simpa [abs_of_nonneg hs_nonneg, abs_of_nonneg ha_nonneg] using hs_abs
      · simpa [abs_of_nonneg ha_nonneg, abs_of_nonneg hs_nonneg] using ha_abs
    · rcases hnonpos with ⟨ha_nonpos, hs_nonpos⟩
      right
      constructor
      · simpa [abs_of_nonpos hs_nonpos, abs_of_nonpos ha_nonpos] using hs_abs
      · simpa [abs_of_nonpos ha_nonpos, abs_of_nonpos hs_nonpos] using ha_abs
  exact
    FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_ratio_bounds
      fmt ha (by simpa [s] using hsigned)

/-- Same-sign interval control for the first rounded sum implies the absolute
ratio bounds needed for the finite FastTwoSum line-2 field.

For nonnegative inputs the interval is `a <= s <= a+b`; for nonpositive inputs
it is `a+b <= s <= a`.  The remaining proof work is to obtain that interval
fact from the concrete base-2 rounder. -/
theorem FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_first_sum_interval
    (fmt : FloatingPointFormat) {a b : ℝ}
    (ha : fmt.finiteSystem a)
    (hinterval :
      let s := fmt.finiteRoundToEvenOp BasicOp.add a b
      (0 ≤ a ∧ 0 ≤ b ∧ |b| < |a| ∧ a ≤ s ∧ s ≤ a + b) ∨
      (a ≤ 0 ∧ b ≤ 0 ∧ |b| < |a| ∧ a + b ≤ s ∧ s ≤ a)) :
    fmt.finiteSystem
      (a - fmt.finiteRoundToEvenOp BasicOp.add a b) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hinterval' :
      (0 ≤ a ∧ 0 ≤ b ∧ |b| < |a| ∧ a ≤ s ∧ s ≤ a + b) ∨
      (a ≤ 0 ∧ b ≤ 0 ∧ |b| < |a| ∧ a + b ≤ s ∧ s ≤ a) := by
    simpa [s] using hinterval
  have hbounds :
      ((0 ≤ a ∧ 0 ≤ s) ∨ (a ≤ 0 ∧ s ≤ 0)) ∧
        |s| ≤ 2 * |a| ∧ |a| ≤ 2 * |s| := by
    rcases hinterval' with hpos | hneg
    · rcases hpos with ⟨ha_nonneg, hb_nonneg, hab_abs, has, hsab⟩
      have hb_lt_a : b < a := by
        simpa [abs_of_nonneg hb_nonneg, abs_of_nonneg ha_nonneg] using hab_abs
      have hs_nonneg : 0 ≤ s := le_trans ha_nonneg has
      refine ⟨Or.inl ⟨ha_nonneg, hs_nonneg⟩, ?_, ?_⟩
      · have hs_le_two_a : s ≤ 2 * a := by
          linarith
        simpa [abs_of_nonneg hs_nonneg, abs_of_nonneg ha_nonneg] using hs_le_two_a
      · have ha_le_two_s : a ≤ 2 * s := by
          linarith
        simpa [abs_of_nonneg ha_nonneg, abs_of_nonneg hs_nonneg] using ha_le_two_s
    · rcases hneg with ⟨ha_nonpos, hb_nonpos, hab_abs, habs, hsa⟩
      have hneg_b_lt_neg_a : -b < -a := by
        simpa [abs_of_nonpos hb_nonpos, abs_of_nonpos ha_nonpos] using hab_abs
      have hs_nonpos : s ≤ 0 := le_trans hsa ha_nonpos
      refine ⟨Or.inr ⟨ha_nonpos, hs_nonpos⟩, ?_, ?_⟩
      · have hneg_s_le_two_neg_a : -s ≤ 2 * (-a) := by
          linarith
        simpa [abs_of_nonpos hs_nonpos, abs_of_nonpos ha_nonpos] using
          hneg_s_le_two_neg_a
      · have hneg_a_le_two_neg_s : -a ≤ 2 * (-s) := by
          linarith
        simpa [abs_of_nonpos ha_nonpos, abs_of_nonpos hs_nonpos] using
          hneg_a_le_two_neg_s
  exact
    FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_abs_ratio_bounds
      fmt ha (by simpa [s] using hbounds)

/-- A small same-sign addend gives the absolute ratio bounds needed for the
finite FastTwoSum line-2 field.

This closes the easy same-sign branch: if the smaller same-sign operand has
magnitude at most one half of the larger operand, nearestness gives `s >= a`
and `s <= a + 2*b` in the nonnegative branch, hence `s <= 2*a`.  The
nonpositive branch follows by round-to-even oddness in base `2`. -/
theorem FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_small_addend
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a)
    (hsmall :
      (0 ≤ a ∧ 0 ≤ b ∧ b ≤ a / 2) ∨
      (a ≤ 0 ∧ b ≤ 0 ∧ -b ≤ (-a) / 2)) :
    fmt.finiteSystem
      (a - fmt.finiteRoundToEvenOp BasicOp.add a b) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hbeta_even : FloatingPointFormat.evenMantissa fmt.beta := by
    unfold FloatingPointFormat.evenMantissa
    omega
  have hbounds :
      ((0 ≤ a ∧ 0 ≤ s) ∨ (a ≤ 0 ∧ s ≤ 0)) ∧
        |s| ≤ 2 * |a| ∧ |a| ≤ 2 * |s| := by
    rcases hsmall with hpos | hneg
    · rcases hpos with ⟨ha_nonneg, hb_nonneg, hb_half⟩
      have has : a ≤ s := by
        simpa [s] using
          fmt.finiteRoundToEvenOp_add_ge_left_of_finiteSystem_of_nonneg
            ha hb_nonneg
      have hs_le : s ≤ a + 2 * b := by
        simpa [s] using
          fmt.finiteRoundToEvenOp_add_le_left_add_two_mul_right_of_finiteSystem_of_nonneg
            ha hb_nonneg
      have hs_nonneg : 0 ≤ s := le_trans ha_nonneg has
      refine ⟨Or.inl ⟨ha_nonneg, hs_nonneg⟩, ?_, ?_⟩
      · have hs_le_two_a : s ≤ 2 * a := by
          linarith
        simpa [abs_of_nonneg hs_nonneg, abs_of_nonneg ha_nonneg] using hs_le_two_a
      · have ha_le_two_s : a ≤ 2 * s := by
          linarith
        simpa [abs_of_nonneg ha_nonneg, abs_of_nonneg hs_nonneg] using ha_le_two_s
    · rcases hneg with ⟨ha_nonpos, hb_nonpos, hb_half⟩
      let sp := fmt.finiteRoundToEvenOp BasicOp.add (-a) (-b)
      have hneg_a_fin : fmt.finiteSystem (-a) := fmt.finiteSystem_neg ha
      have hneg_b_nonneg : 0 ≤ -b := by linarith
      have hsp_ge : -a ≤ sp := by
        simpa [sp] using
          fmt.finiteRoundToEvenOp_add_ge_left_of_finiteSystem_of_nonneg
            hneg_a_fin hneg_b_nonneg
      have hsp_le : sp ≤ -a + 2 * (-b) := by
        simpa [sp] using
          fmt.finiteRoundToEvenOp_add_le_left_add_two_mul_right_of_finiteSystem_of_nonneg
            hneg_a_fin hneg_b_nonneg
      have hsp_nonneg : 0 ≤ sp := le_trans (by linarith) hsp_ge
      have hs_eq_neg_sp : s = -sp := by
        dsimp [s, sp, FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact]
        have hsum : a + b = -((-a) + (-b)) := by ring
        rw [hsum]
        simpa using
          fmt.finiteRoundToEven_neg hbeta_even ht ((-a) + (-b))
      have hs_nonpos : s ≤ 0 := by
        rw [hs_eq_neg_sp]
        linarith
      refine ⟨Or.inr ⟨ha_nonpos, hs_nonpos⟩, ?_, ?_⟩
      · have hneg_s_le_two_neg_a : -s ≤ 2 * (-a) := by
          rw [hs_eq_neg_sp]
          linarith
        simpa [abs_of_nonpos hs_nonpos, abs_of_nonpos ha_nonpos] using
          hneg_s_le_two_neg_a
      · have hneg_a_le_two_neg_s : -a ≤ 2 * (-s) := by
          rw [hs_eq_neg_sp]
          linarith
        simpa [abs_of_nonpos ha_nonpos, abs_of_nonpos hs_nonpos] using
          hneg_a_le_two_neg_s
  exact
    FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_abs_ratio_bounds
      fmt ha (by simpa [s] using hbounds)

/-- Same-sign source operands satisfying `|b| < |a|` give the line-2
representability field for the finite FastTwoSum certificate.

For nonnegative operands, nearestness gives `a <= s`; an upper bound `s <= 2*a`
comes either from the finite candidate `2*a`, when it is in range, or from the
global finite-output bound when `2*a` is beyond the largest finite magnitude.
The nonpositive branch reduces to the nonnegative one by base-2 oddness of
round-to-even. -/
theorem FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_abs_order
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a)
    (hab : |b| < |a|)
    (hsign : (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0)) :
    fmt.finiteSystem
      (a - fmt.finiteRoundToEvenOp BasicOp.add a b) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hbeta_even : FloatingPointFormat.evenMantissa fmt.beta := by
    unfold FloatingPointFormat.evenMantissa
    omega
  have hbounds :
      ((0 ≤ a ∧ 0 ≤ s) ∨ (a ≤ 0 ∧ s ≤ 0)) ∧
        |s| ≤ 2 * |a| ∧ |a| ≤ 2 * |s| := by
    rcases hsign with hpos | hneg
    · rcases hpos with ⟨ha_nonneg, hb_nonneg⟩
      have has : a ≤ s := by
        simpa [s] using
          fmt.finiteRoundToEvenOp_add_ge_left_of_finiteSystem_of_nonneg
            ha hb_nonneg
      have hb_le_a : b ≤ a := by
        have hlt : b < a := by
          simpa [abs_of_nonneg hb_nonneg, abs_of_nonneg ha_nonneg] using hab
        exact le_of_lt hlt
      have hs_nonneg : 0 ≤ s := le_trans ha_nonneg has
      have hs_le_two_a : s ≤ 2 * a := by
        by_cases htwo_le_max : 2 * a ≤ fmt.maxFiniteMagnitude
        · have htwo_nonneg : 0 ≤ 2 * a := by nlinarith
          have htwo_fin : fmt.finiteSystem (2 * a) :=
            fmt.finiteSystem_two_mul_of_abs_le_maxFiniteMagnitude hbeta ha
              (by simpa [abs_of_nonneg htwo_nonneg] using htwo_le_max)
          have hsum_le : a + b ≤ 2 * a := by linarith
          simpa [s] using
            fmt.finiteRoundToEvenOp_add_le_of_exact_le_finiteSystem
              htwo_fin hsum_le
        · have hmax_lt : fmt.maxFiniteMagnitude < 2 * a :=
            lt_of_not_ge htwo_le_max
          have hs_abs_le :
              |s| ≤ fmt.maxFiniteMagnitude := by
            simpa [s] using
              fmt.finiteSystem_abs_le_maxFiniteMagnitude
                (fmt.finiteRoundToEvenOp_finiteSystem BasicOp.add a b)
          have hs_le_max : s ≤ fmt.maxFiniteMagnitude := by
            simpa [abs_of_nonneg hs_nonneg] using hs_abs_le
          exact le_of_lt (lt_of_le_of_lt hs_le_max hmax_lt)
      refine ⟨Or.inl ⟨ha_nonneg, hs_nonneg⟩, ?_, ?_⟩
      · simpa [abs_of_nonneg hs_nonneg, abs_of_nonneg ha_nonneg] using
          hs_le_two_a
      · have ha_le_two_s : a ≤ 2 * s := by
          nlinarith
        simpa [abs_of_nonneg ha_nonneg, abs_of_nonneg hs_nonneg] using
          ha_le_two_s
    · rcases hneg with ⟨ha_nonpos, hb_nonpos⟩
      let sp := fmt.finiteRoundToEvenOp BasicOp.add (-a) (-b)
      have hneg_a_fin : fmt.finiteSystem (-a) := fmt.finiteSystem_neg ha
      have hneg_a_nonneg : 0 ≤ -a := by linarith
      have hneg_b_nonneg : 0 ≤ -b := by linarith
      have hneg_b_le_neg_a : -b ≤ -a := by
        have hlt : -b < -a := by
          simpa [abs_of_nonpos hb_nonpos, abs_of_nonpos ha_nonpos] using hab
        exact le_of_lt hlt
      have hsp_ge : -a ≤ sp := by
        simpa [sp] using
          fmt.finiteRoundToEvenOp_add_ge_left_of_finiteSystem_of_nonneg
            hneg_a_fin hneg_b_nonneg
      have hsp_nonneg : 0 ≤ sp := le_trans hneg_a_nonneg hsp_ge
      have hsp_le_two_neg_a : sp ≤ 2 * (-a) := by
        by_cases htwo_le_max : 2 * (-a) ≤ fmt.maxFiniteMagnitude
        · have htwo_nonneg : 0 ≤ 2 * (-a) := by nlinarith
          have htwo_abs_le : |2 * (-a)| ≤ fmt.maxFiniteMagnitude := by
            rw [abs_of_nonneg htwo_nonneg]
            exact htwo_le_max
          have htwo_fin : fmt.finiteSystem (2 * (-a)) :=
            fmt.finiteSystem_two_mul_of_abs_le_maxFiniteMagnitude hbeta hneg_a_fin
              htwo_abs_le
          have hsum_le : (-a) + (-b) ≤ 2 * (-a) := by linarith
          simpa [sp] using
            fmt.finiteRoundToEvenOp_add_le_of_exact_le_finiteSystem
              htwo_fin hsum_le
        · have hmax_lt : fmt.maxFiniteMagnitude < 2 * (-a) :=
            lt_of_not_ge htwo_le_max
          have hsp_abs_le :
              |sp| ≤ fmt.maxFiniteMagnitude := by
            simpa [sp] using
              fmt.finiteSystem_abs_le_maxFiniteMagnitude
                (fmt.finiteRoundToEvenOp_finiteSystem BasicOp.add (-a) (-b))
          have hsp_le_max : sp ≤ fmt.maxFiniteMagnitude := by
            simpa [abs_of_nonneg hsp_nonneg] using hsp_abs_le
          exact le_of_lt (lt_of_le_of_lt hsp_le_max hmax_lt)
      have hs_eq_neg_sp : s = -sp := by
        dsimp [s, sp, FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact]
        have hsum : a + b = -((-a) + (-b)) := by ring
        rw [hsum]
        simpa using
          fmt.finiteRoundToEven_neg hbeta_even ht ((-a) + (-b))
      have hs_nonpos : s ≤ 0 := by
        rw [hs_eq_neg_sp]
        linarith
      refine ⟨Or.inr ⟨ha_nonpos, hs_nonpos⟩, ?_, ?_⟩
      · have hneg_s_le_two_neg_a : -s ≤ 2 * (-a) := by
          have hneg_s_eq_sp : -s = sp := by
            rw [hs_eq_neg_sp]
            ring
          simpa [hneg_s_eq_sp] using hsp_le_two_neg_a
        simpa [abs_of_nonpos hs_nonpos, abs_of_nonpos ha_nonpos] using
          hneg_s_le_two_neg_a
      · have hneg_a_le_two_neg_s : -a ≤ 2 * (-s) := by
          rw [hs_eq_neg_sp]
          nlinarith
        simpa [abs_of_nonpos ha_nonpos, abs_of_nonpos hs_nonpos] using
          hneg_a_le_two_neg_s
  exact
    FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_abs_ratio_bounds
      fmt ha (by simpa [s] using hbounds)

/-- Base-2 absolute-order FastTwoSum certificate from the signed Sterbenz
line-2 branch.

This removes the old need for a second Sterbenz proof for `(a+b)-s`: the true
roundoff-error field is supplied by the base-2 rounded-add error theorem. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_order_of_signed_sterbenz_a_sub_s
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hsub_sterbenz :
      fmt.sterbenzRatioCondition a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) ∨
        fmt.sterbenzRatioCondition (-a)
          (-(fmt.finiteRoundToEvenOp BasicOp.add a b))) :
    FastTwoSumFiniteCertificate fmt a b :=
  FastTwoSumFiniteCertificate.of_base2_abs_order_of_finite_a_sub_s
    fmt hbeta ht ha hb hab habRange
    (FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz
      fmt ha hsub_sterbenz)

/-- Base-2 absolute-order FastTwoSum certificate from the strict Sterbenz or
endpoint-inclusive line-2 branch.

This is the certificate-level form of the corrected C4.4 route exposed by the
strict-Sterbenz endpoint counterexample: strict signed Sterbenz remains enough
away from the endpoints, while the two endpoint equalities close `a-s`
representability directly. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_order_of_signed_sterbenz_or_endpoint_a_sub_s
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hsub :
      (fmt.sterbenzRatioCondition a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) ∨
        fmt.sterbenzRatioCondition (-a)
          (-(fmt.finiteRoundToEvenOp BasicOp.add a b))) ∨
      fmt.finiteRoundToEvenOp BasicOp.add a b = 2 * a ∨
      a = 2 * fmt.finiteRoundToEvenOp BasicOp.add a b) :
    FastTwoSumFiniteCertificate fmt a b :=
  FastTwoSumFiniteCertificate.of_base2_abs_order_of_finite_a_sub_s
    fmt hbeta ht ha hb hab habRange
    (FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz_or_endpoint
      fmt ha hsub)

/-- Base-2 absolute-order FastTwoSum certificate from non-strict signed ratio
bounds on `a` and the rounded first sum.

The non-strict bounds are immediately split into strict signed Sterbenz or one
of the two endpoint equalities before reusing the closed base-2 rounded-add
error theorem. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_order_of_signed_ratio_bounds_a_sub_s
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hbounds :
      let s := fmt.finiteRoundToEvenOp BasicOp.add a b
      (s ≤ 2 * a ∧ a ≤ 2 * s) ∨
      (-s ≤ 2 * (-a) ∧ -a ≤ 2 * (-s))) :
    FastTwoSumFiniteCertificate fmt a b :=
  FastTwoSumFiniteCertificate.of_base2_abs_order_of_finite_a_sub_s
    fmt hbeta ht ha hb hab habRange
    (FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_ratio_bounds
      fmt ha hbounds)

/-- Base-2 absolute-order FastTwoSum certificate from same-sign absolute ratio
bounds on `a` and the rounded first sum.

This source-facing wrapper composes the same-sign absolute-ratio adapter with
the closed rounded-add error theorem. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_order_of_same_sign_abs_ratio_bounds_a_sub_s
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hbounds :
      let s := fmt.finiteRoundToEvenOp BasicOp.add a b
      (((0 ≤ a ∧ 0 ≤ s) ∨ (a ≤ 0 ∧ s ≤ 0)) ∧
        |s| ≤ 2 * |a| ∧ |a| ≤ 2 * |s|)) :
    FastTwoSumFiniteCertificate fmt a b :=
  FastTwoSumFiniteCertificate.of_base2_abs_order_of_finite_a_sub_s
    fmt hbeta ht ha hb hab habRange
    (FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_abs_ratio_bounds
      fmt ha hbounds)

/-- Base-2 absolute-order FastTwoSum certificate from same-sign interval
control of the first rounded sum.

This packages a source-shaped route: once `s = fl(a+b)` is known to lie between
the larger same-sign operand `a` and the exact same-sign sum, the same-sign
absolute ratio-bound branch supplies the `a-s` certificate field. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_order_of_same_sign_first_sum_interval_a_sub_s
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hinterval :
      let s := fmt.finiteRoundToEvenOp BasicOp.add a b
      (0 ≤ a ∧ 0 ≤ b ∧ |b| < |a| ∧ a ≤ s ∧ s ≤ a + b) ∨
      (a ≤ 0 ∧ b ≤ 0 ∧ |b| < |a| ∧ a + b ≤ s ∧ s ≤ a)) :
    FastTwoSumFiniteCertificate fmt a b :=
  FastTwoSumFiniteCertificate.of_base2_abs_order_of_finite_a_sub_s
    fmt hbeta ht ha hb hab habRange
    (FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_first_sum_interval
      fmt ha hinterval)

/-- Base-2 absolute-order FastTwoSum certificate for the easy same-sign
small-addend branch.

If the same-sign addend has magnitude at most one half of the larger operand,
the one-sided nearestness bounds give the signed ratio bounds for `a` and
`s = fl(a+b)`, while the closed rounded-add error theorem supplies the other
certificate field. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_order_of_same_sign_small_addend_a_sub_s
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hsmall :
      (0 ≤ a ∧ 0 ≤ b ∧ b ≤ a / 2) ∨
      (a ≤ 0 ∧ b ≤ 0 ∧ -b ≤ (-a) / 2)) :
    FastTwoSumFiniteCertificate fmt a b :=
  FastTwoSumFiniteCertificate.of_base2_abs_order_of_finite_a_sub_s
    fmt hbeta ht ha hb hab habRange
    (FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_small_addend
      fmt hbeta ht ha hsmall)

/-- Base-2 absolute-order FastTwoSum certificate for the full same-sign source
branch.

Under the source magnitude order `|b| < |a|`, same-sign operands already give
the ratio bounds for `a` and `s = fl(a+b)` needed by the line-2 certificate
field; the closed rounded-add error theorem supplies the other field. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_order_of_same_sign_a_sub_s
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hsign : (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0)) :
    FastTwoSumFiniteCertificate fmt a b :=
  FastTwoSumFiniteCertificate.of_base2_abs_order_of_finite_a_sub_s
    fmt hbeta ht ha hb hab habRange
    (FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_abs_order
      fmt hbeta ht ha hab hsign)

/-- Base-2 absolute-order FastTwoSum certificate for the inexact
opposite-sign branch.

The near-magnitude exact-add branch has already been ruled out by the inexact
first sum, so the remaining opposite-sign case supplies the signed ratio bounds
needed for `a-s` representability. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_order_of_opposite_sign_inexact_a_sub_s
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hsign : (0 ≤ a ∧ b ≤ 0) ∨ (a ≤ 0 ∧ 0 ≤ b))
    (hinexact : fmt.finiteRoundToEvenOp BasicOp.add a b ≠ a + b) :
    FastTwoSumFiniteCertificate fmt a b :=
  FastTwoSumFiniteCertificate.of_base2_abs_order_of_signed_ratio_bounds_a_sub_s
    fmt hbeta ht ha hb hab habRange
    (FastTwoSumFiniteCertificate.signed_ratio_bounds_of_opposite_sign_abs_order_inexact
      fmt hbeta ht ha hb hab habRange hsign hinexact)

/-- Base-2 absolute-order FastTwoSum certificate for an inexact first add.

This closes the remaining all-sign inexact branch of the correction formula:
same-sign operands use the closed same-sign source theorem, and opposite-sign
operands use the far-magnitude signed-ratio split after the near-magnitude
exact branch is excluded by `hinexact`. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_gt_of_inexact_add
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hinexact : fmt.finiteRoundToEvenOp BasicOp.add a b ≠ a + b) :
    FastTwoSumFiniteCertificate fmt a b := by
  by_cases ha_nonneg : 0 ≤ a
  · by_cases hb_nonneg : 0 ≤ b
    · exact
        FastTwoSumFiniteCertificate.of_base2_abs_order_of_same_sign_a_sub_s
          fmt hbeta ht ha hb hab habRange
          (Or.inl ⟨ha_nonneg, hb_nonneg⟩)
    · have hb_nonpos : b ≤ 0 := le_of_not_ge hb_nonneg
      exact
        FastTwoSumFiniteCertificate.of_base2_abs_order_of_opposite_sign_inexact_a_sub_s
          fmt hbeta ht ha hb hab habRange
          (Or.inl ⟨ha_nonneg, hb_nonpos⟩) hinexact
  · have ha_nonpos : a ≤ 0 := le_of_not_ge ha_nonneg
    by_cases hb_nonpos : b ≤ 0
    · exact
        FastTwoSumFiniteCertificate.of_base2_abs_order_of_same_sign_a_sub_s
          fmt hbeta ht ha hb hab habRange
          (Or.inr ⟨ha_nonpos, hb_nonpos⟩)
    · have hb_nonneg : 0 ≤ b := le_of_not_ge hb_nonpos
      exact
        FastTwoSumFiniteCertificate.of_base2_abs_order_of_opposite_sign_inexact_a_sub_s
          fmt hbeta ht ha hb hab habRange
          (Or.inr ⟨ha_nonpos, hb_nonneg⟩) hinexact

/-- Base-2 absolute-order FastTwoSum finite certificate.

This is the finite-format certificate form of Higham equation (4.7)'s binary
correction-formula exactness route: the exact-first-add branch uses
`FastTwoSumFiniteCertificate.of_exact_add`, while the inexact branch uses
`FastTwoSumFiniteCertificate.of_base2_abs_gt_of_inexact_add`. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_gt
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b)) :
    FastTwoSumFiniteCertificate fmt a b := by
  by_cases hadd : fmt.finiteRoundToEvenOp BasicOp.add a b = a + b
  · exact FastTwoSumFiniteCertificate.of_exact_add fmt a b hb hadd
  · exact
      FastTwoSumFiniteCertificate.of_base2_abs_gt_of_inexact_add
        fmt hbeta ht ha hb hab habRange hadd

/-- Base-2 FastTwoSum certificate with Higham's non-strict order
`|b| ≤ |a|`.  Equal magnitudes force `b = a` or `b = -a`, so the first
addition is exact (`2a` or `0`) when overflow is excluded by `habRange`. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_le
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| ≤ |a|)
    (habRange : fmt.finiteNormalRange (a + b)) :
    FastTwoSumFiniteCertificate fmt a b := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · exact FastTwoSumFiniteCertificate.of_base2_abs_gt
      fmt hbeta ht ha hb hlt habRange
  · rcases abs_eq_abs.mp heq with hba | hba
    · subst b
      have hfin : fmt.finiteSystem (a + a) := by
        have htwo := fmt.finiteSystem_two_mul_of_abs_le_maxFiniteMagnitude
          hbeta ha (by simpa [two_mul] using habRange.2)
        simpa [two_mul] using htwo
      have hadd :
          fmt.finiteRoundToEvenOp BasicOp.add a a = a + a := by
        simpa [BasicOp.exact] using
          fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
            (op := BasicOp.add) (x := a) (y := a) hfin
      exact FastTwoSumFiniteCertificate.of_exact_add fmt a a ha hadd
    · subst b
      have hfin : fmt.finiteSystem (a + -a) := by
        simpa using fmt.finiteSystem_zero
      have hadd :
          fmt.finiteRoundToEvenOp BasicOp.add a (-a) = a + -a := by
        simpa [BasicOp.exact] using
          fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
            (op := BasicOp.add) (x := a) (y := -a) hfin
      exact FastTwoSumFiniteCertificate.of_exact_add fmt a (-a)
        (fmt.finiteSystem_neg ha) hadd

/-- If the finite FastTwoSum certificate supplies representability of the
intermediate subtraction and the true local error, then Higham equation
(4.7)'s exactness conclusion follows for the finite round-to-even trace. -/
theorem finiteCorrectionFormulaTrace_exact_of_fastTwoSumFiniteCertificate
    (fmt : FloatingPointFormat) (a b : ℝ)
    (hcert : FastTwoSumFiniteCertificate fmt a b) :
    CorrectionFormulaTrace.exact a b
      (finiteCorrectionFormulaTrace fmt a b) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hsub :
      fmt.finiteRoundToEvenOp BasicOp.sub a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) =
        a - fmt.finiteRoundToEvenOp BasicOp.add a b := by
    have hsub_finite :
        fmt.finiteSystem
          (BasicOp.exact BasicOp.sub a
            (fmt.finiteRoundToEvenOp BasicOp.add a b)) := by
      simpa [BasicOp.exact, s] using hcert.finite_a_sub_s
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub) (x := a)
        (y := fmt.finiteRoundToEvenOp BasicOp.add a b) hsub_finite)
  have hadd :
      fmt.finiteSystem
        ((a - fmt.finiteRoundToEvenOp BasicOp.add a b) + b) := by
    have hrewrite :
        (a - s) + b = (a + b) - s := by ring
    simpa [s, hrewrite] using hcert.finite_error
  exact finiteCorrectionFormulaTrace_exact_of_exact_sub_and_finite_error_add
    fmt a b hsub hadd

/-- Exact-first-add branch of Higham equation (4.7)'s finite round-to-even
correction formula.

When `s = fl(a+b)` is already the exact real sum and `b` is finite
representable, the displayed correction formula recovers the local error
exactly. -/
theorem finiteCorrectionFormulaTrace_exact_of_exact_add
    (fmt : FloatingPointFormat) (a b : ℝ)
    (hb : fmt.finiteSystem b)
    (hadd :
      fmt.finiteRoundToEvenOp BasicOp.add a b = a + b) :
    CorrectionFormulaTrace.exact a b
      (finiteCorrectionFormulaTrace fmt a b) :=
  finiteCorrectionFormulaTrace_exact_of_fastTwoSumFiniteCertificate fmt a b
    (FastTwoSumFiniteCertificate.of_exact_add fmt a b hb hadd)

/-- Higham equation (4.7) for the concrete finite binary round-to-even
correction-formula trace. -/
theorem finiteCorrectionFormulaTrace_exact_of_base2_abs_gt
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b)) :
    CorrectionFormulaTrace.exact a b
      (finiteCorrectionFormulaTrace fmt a b) :=
  finiteCorrectionFormulaTrace_exact_of_fastTwoSumFiniteCertificate
    fmt a b
    (FastTwoSumFiniteCertificate.of_base2_abs_gt
      fmt hbeta ht ha hb hab habRange)

/-- Higham equation (4.7) with the source's non-strict magnitude hypothesis
`|a| ≥ |b|`.

The strict branch is `finiteCorrectionFormulaTrace_exact_of_base2_abs_gt`.
When the magnitudes tie, `b = a` or `b = -a`: the first sum is respectively
`2a` or `0`, hence is exactly representable (the normal-range hypothesis rules
out overflow in the doubling branch), and the exact-add certificate closes the
displayed correction trace.  This packages the equality case that was formerly
only documented as an informal side branch. -/
theorem finiteCorrectionFormulaTrace_exact_of_base2_abs_le
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| ≤ |a|)
    (habRange : fmt.finiteNormalRange (a + b)) :
    CorrectionFormulaTrace.exact a b
      (finiteCorrectionFormulaTrace fmt a b) :=
  finiteCorrectionFormulaTrace_exact_of_fastTwoSumFiniteCertificate fmt a b
    (FastTwoSumFiniteCertificate.of_base2_abs_le
      fmt hbeta ht ha hb hab habRange)

/-- A deliberately coarse abstract `FPModel` showing that the standard
relative-error model alone does not imply Higham equation (4.7).  Addition
from zero is exact, as required by `FPModel`; all other primitive operations
may round to zero with unit roundoff `u = 1`. -/
noncomputable def correctionFormulaAbstractCounterexampleFPModel : FPModel where
  u := 1
  u_nonneg := by norm_num
  fl_add := fun x y => if x = 0 then y else 0
  fl_sub := fun _ _ => 0
  fl_mul := fun _ _ => 0
  fl_div := fun _ _ => 0
  fl_sqrt := fun _ => 0
  fl_add_zero := by
    intro x
    simp
  model_add := by
    intro x y
    by_cases hx : x = 0
    · subst x
      refine ⟨0, by norm_num, ?_⟩
      simp
    · refine ⟨-1, by norm_num, ?_⟩
      simp [hx]
  model_sub := by
    intro x y
    refine ⟨-1, by norm_num, ?_⟩
    ring_nf
  model_mul := by
    intro x y
    refine ⟨-1, by norm_num, ?_⟩
    ring_nf
  model_div := by
    intro x y _hy
    refine ⟨-1, by norm_num, ?_⟩
    ring_nf
  model_sqrt := by
    intro x _hx
    refine ⟨-1, by norm_num, ?_⟩
    ring_nf

/-- The counterexample still satisfies the source magnitude precondition
`|a| > |b|`. -/
theorem correctionFormulaAbstractCounterexample_abs_order :
    |(-7 / 8 : ℝ)| < |(1 : ℝ)| := by
  norm_num

/-- Under the abstract standard model alone, the correction formula need not
recover the exact local error.  This separates the closed source-level trace
from the still-open finite base-2 exactness theorem. -/
theorem correctionFormulaAbstractCounterexample_not_exact :
    ¬ CorrectionFormulaTrace.exact (1 : ℝ) (-7 / 8)
      (correctionFormulaTrace correctionFormulaAbstractCounterexampleFPModel
        (1 : ℝ) (-7 / 8)) := by
  norm_num [CorrectionFormulaTrace.exact, correctionFormulaTrace,
    correctionFormulaAbstractCounterexampleFPModel]

/-! ## No-guard local correction-formula traces -/

/-- Source-level local correction trace under the no-guard model.  The extra
field `aMinusS` records the rounded intermediate subtraction in the displayed
evaluation order: `s = fl(a+b)`, `aMinusS = fl(a-s)`, `e = fl(aMinusS+b)`. -/
structure NoGuardCorrectionFormulaTrace where
  s : ℝ
  aMinusS : ℝ
  e : ℝ

namespace NoGuardCorrectionFormulaTrace

/-- The source exactness conclusion analogous to Higham equation (4.7). -/
def exact (a b : ℝ) (t : NoGuardCorrectionFormulaTrace) : Prop :=
  a + b = t.s + t.e

/-- The underlying no-guard local-operation witnesses for the displayed
correction-formula evaluation order. -/
def model (u a b : ℝ) (t : NoGuardCorrectionFormulaTrace) : Prop :=
  (∃ α β : ℝ, noGuardAddWitness t.s a b u α β) ∧
    (∃ α β : ℝ, noGuardSubWitness t.aMinusS a t.s u α β) ∧
      ∃ α β : ℝ, noGuardAddWitness t.e t.aMinusS b u α β

/-- Forget the no-guard subtraction intermediate and view the trace as the
ordinary correction-formula pair `(s,e)`. -/
def toCorrectionFormulaTrace (t : NoGuardCorrectionFormulaTrace) :
    CorrectionFormulaTrace :=
  { s := t.s, e := t.e }

end NoGuardCorrectionFormulaTrace

/-- The displayed local correction-formula trace evaluated in a supplied
no-guard floating-point model. -/
noncomputable def noGuardCorrectionFormulaTrace
    (fp : NoGuardFPModel) (a b : ℝ) : NoGuardCorrectionFormulaTrace :=
  let s := fp.fl_add a b
  let aMinusS := fp.fl_sub a s
  let e := fp.fl_add aMinusS b
  { s := s, aMinusS := aMinusS, e := e }

/-- The no-guard `s = fl(a+b)` assignment. -/
theorem noGuardCorrectionFormulaTrace_s
    (fp : NoGuardFPModel) (a b : ℝ) :
    (noGuardCorrectionFormulaTrace fp a b).s = fp.fl_add a b := by
  rfl

/-- The no-guard `aMinusS = fl(a-s)` assignment. -/
theorem noGuardCorrectionFormulaTrace_aMinusS
    (fp : NoGuardFPModel) (a b : ℝ) :
    (noGuardCorrectionFormulaTrace fp a b).aMinusS =
      fp.fl_sub a (noGuardCorrectionFormulaTrace fp a b).s := by
  rfl

/-- The no-guard `e = fl(aMinusS+b)` assignment. -/
theorem noGuardCorrectionFormulaTrace_e
    (fp : NoGuardFPModel) (a b : ℝ) :
    (noGuardCorrectionFormulaTrace fp a b).e =
      fp.fl_add (noGuardCorrectionFormulaTrace fp a b).aMinusS b := by
  rfl

/-- A no-guard model supplies exactly the local witnesses recorded by
`NoGuardCorrectionFormulaTrace.model`. -/
theorem noGuardCorrectionFormulaTrace_model
    (fp : NoGuardFPModel) (a b : ℝ) :
    NoGuardCorrectionFormulaTrace.model fp.u a b
      (noGuardCorrectionFormulaTrace fp a b) := by
  dsimp [NoGuardCorrectionFormulaTrace.model, noGuardCorrectionFormulaTrace]
  constructor
  · simpa using fp.model_add a b
  constructor
  · simpa using fp.model_sub a (fp.fl_add a b)
  · simpa using fp.model_add (fp.fl_sub a (fp.fl_add a b)) b

/-- Concrete local no-guard trace showing that the no-guard model alone does
not force Higham equation (4.7).  The numbers have `|1| > |-7/8|`; the two
additions use permitted no-guard input perturbations with `u = 1/4`, while
the intermediate subtraction is exact. -/
noncomputable def noGuardCorrectionFormulaCounterexample :
    NoGuardCorrectionFormulaTrace :=
  { s := 1 / 4, aMinusS := 3 / 4, e := 0 }

/-- The counterexample satisfies the source magnitude precondition
`|a| > |b|`. -/
theorem noGuardCorrectionFormulaCounterexample_abs_order :
    |(-7 / 8 : ℝ)| < |(1 : ℝ)| := by
  norm_num

/-- The counterexample obeys the local no-guard operation model with
`u = 1/4`. -/
theorem noGuardCorrectionFormulaCounterexample_model :
    NoGuardCorrectionFormulaTrace.model (1 / 4 : ℝ) (1 : ℝ) (-7 / 8)
      noGuardCorrectionFormulaCounterexample := by
  dsimp [NoGuardCorrectionFormulaTrace.model,
    noGuardCorrectionFormulaCounterexample]
  constructor
  · refine ⟨0, -1 / 7, ?_, ?_, ?_⟩ <;> norm_num [noGuardAddWitness]
  constructor
  · refine ⟨0, 0, ?_, ?_, ?_⟩ <;> norm_num [noGuardSubWitness]
  · refine ⟨0, -1 / 7, ?_, ?_, ?_⟩ <;> norm_num [noGuardAddWitness]

/-- In that local no-guard trace, the equation `a+b = s+e` is false. -/
theorem noGuardCorrectionFormulaCounterexample_not_exact :
    ¬ NoGuardCorrectionFormulaTrace.exact (1 : ℝ) (-7 / 8)
      noGuardCorrectionFormulaCounterexample := by
  norm_num [NoGuardCorrectionFormulaTrace.exact,
    noGuardCorrectionFormulaCounterexample]

/-- The same counterexample refutes the ordinary `(s,e)` exactness predicate
after forgetting the no-guard intermediate. -/
theorem noGuardCorrectionFormulaCounterexample_toCorrectionFormulaTrace_not_exact :
    ¬ CorrectionFormulaTrace.exact (1 : ℝ) (-7 / 8)
      (NoGuardCorrectionFormulaTrace.toCorrectionFormulaTrace
        noGuardCorrectionFormulaCounterexample) := by
  norm_num [CorrectionFormulaTrace.exact,
    NoGuardCorrectionFormulaTrace.toCorrectionFormulaTrace,
    noGuardCorrectionFormulaCounterexample]

/-- One source-level Kahan loop trace, including the intermediate `temp` and
`y` values and the updated `s` and `e`. -/
structure KahanStepTrace where
  temp : ℝ
  y : ℝ
  s : ℝ
  e : ℝ

namespace KahanStepTrace

/-- The persistent state after a Kahan step trace. -/
def nextState (t : KahanStepTrace) : KahanState :=
  { s := t.s, e := t.e }

end KahanStepTrace

/-- One rounded Kahan compensated-summation step for input `x`. -/
noncomputable def kahanStepTrace (fp : FPModel) (x : ℝ)
    (state : KahanState) : KahanStepTrace :=
  let temp := state.s
  let y := fp.fl_add x state.e
  let s := fp.fl_add temp y
  let e := fp.fl_add (fp.fl_sub temp s) y
  { temp := temp, y := y, s := s, e := e }

/-- Persistent-state update induced by one Kahan step. -/
noncomputable def kahanStep (fp : FPModel) (x : ℝ)
    (state : KahanState) : KahanState :=
  (kahanStepTrace fp x state).nextState

/-- Bare `FPModel` does not force the first Algorithm 4.2 step from
`s=0,e=0` to ingest a nonzero input exactly.  This counterexample is the same
coarse abstract model used above for the local correction formula: it satisfies
the model's left-zero addition law, but not the right-zero coherence required
by the source finite-format initialization proof. -/
theorem kahanStepTrace_abstractCounterexample_zero :
    kahanStepTrace correctionFormulaAbstractCounterexampleFPModel
        (1 : ℝ) KahanState.zero =
      { temp := 0, y := 0, s := 0, e := 0 } := by
  norm_num [kahanStepTrace, KahanState.zero,
    correctionFormulaAbstractCounterexampleFPModel]

/-- The abstract standard model alone does not prove the source initialization
fact `kahanStep fp x KahanState.zero = {s := x, e := 0}` for all inputs.  The
finite-format theorem `finiteKahanStep_zero_of_finiteSystem` supplies the
coherence needed for concrete round-to-even formats. -/
theorem not_forall_kahanStep_zero_exact :
    ¬ ∀ (fp : FPModel) (x : ℝ),
      kahanStep fp x KahanState.zero = { s := x, e := 0 } := by
  intro h
  have h1 := h correctionFormulaAbstractCounterexampleFPModel (1 : ℝ)
  norm_num [kahanStep, kahanStepTrace, KahanStepTrace.nextState,
    KahanState.zero, correctionFormulaAbstractCounterexampleFPModel] at h1

/-- Concrete non-exact first-step consequence of
`kahanStepTrace_abstractCounterexample_zero`. -/
theorem kahanStep_abstractCounterexample_zero_ne_exact :
    kahanStep correctionFormulaAbstractCounterexampleFPModel
        (1 : ℝ) KahanState.zero ≠ { s := 1, e := 0 } := by
  intro h
  norm_num [kahanStep, kahanStepTrace, KahanStepTrace.nextState,
    KahanState.zero, correctionFormulaAbstractCounterexampleFPModel] at h

/-- A small-unit-roundoff abstract model that is useful for auditing attempted
bare-`FPModel` Kahan routes.  Addition from the left zero is exact, as required
by `FPModel`; every other addition rounds upward by `u`, while subtraction rounds
downward by `u`.

This model is not intended as a concrete finite format.  It records that the
abstract relative-error contract alone permits independent operation-level signs
that finite round-to-even coherence would rule out. -/
noncomputable def kahanBiasedSmallCounterexampleFPModel (u : ℝ) (hu : 0 ≤ u) :
    FPModel where
  u := u
  u_nonneg := hu
  fl_add := fun x y => if x = 0 then y else (x + y) * (1 + u)
  fl_sub := fun x y => (x - y) * (1 - u)
  fl_mul := fun x y => x * y
  fl_div := fun x y => x / y
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := by
    intro x
    simp
  model_add := by
    intro x y
    by_cases hx : x = 0
    · refine ⟨0, ?_, ?_⟩
      · simpa using hu
      · simp [hx]
    · refine ⟨u, ?_, ?_⟩
      · rw [abs_of_nonneg hu]
      · simp [hx]
  model_sub := by
    intro x y
    refine ⟨-u, ?_, ?_⟩
    · rw [abs_neg, abs_of_nonneg hu]
    · ring
  model_mul := by
    intro x y
    refine ⟨0, ?_, ?_⟩
    · simpa using hu
    · ring
  model_div := by
    intro x y _hy
    refine ⟨0, ?_, ?_⟩
    · simpa using hu
    · ring
  model_sqrt := by
    intro x _hx
    refine ⟨0, ?_, ?_⟩
    · simpa using hu
    · ring

/-- Two-term audit input for the small-unit-roundoff Kahan route-elimination
example.  The second term is zero, so any source-weight representation has a
unique coefficient for the first term. -/
def kahanBiasedTwoStepInput : Fin 2 → ℝ :=
  fun i => if i.val = 0 then 1 else 0

/-- Abstract exact-zero-path bridge for the first Algorithm 4.2 step.

The theorem isolates the exact coherence needed to start Kahan's recurrence
from `s=0,e=0`: right-zero addition for the incoming input, exact subtraction
`0-x`, and exact cancellation `(-x)+x`.  Concrete finite round-to-even formats
provide these facts via representability lemmas below; bare `FPModel` does not,
as shown by `not_forall_kahanStep_zero_exact`. -/
theorem kahanStepTrace_zero_of_exact_zero_path
    (fp : FPModel) {x : ℝ}
    (haddRight : fp.fl_add x 0 = x)
    (hsub : fp.fl_sub 0 x = -x)
    (hcancel : fp.fl_add (-x) x = 0) :
    kahanStepTrace fp x KahanState.zero =
      { temp := 0, y := x, s := x, e := 0 } := by
  simp [kahanStepTrace, KahanState.zero, haddRight, fp.fl_add_zero,
    hsub, hcancel]

/-- Persistent-state form of `kahanStepTrace_zero_of_exact_zero_path`. -/
theorem kahanStep_zero_of_exact_zero_path
    (fp : FPModel) {x : ℝ}
    (haddRight : fp.fl_add x 0 = x)
    (hsub : fp.fl_sub 0 x = -x)
    (hcancel : fp.fl_add (-x) x = 0) :
    kahanStep fp x KahanState.zero = { s := x, e := 0 } := by
  have htrace :=
    kahanStepTrace_zero_of_exact_zero_path
      fp haddRight hsub hcancel
  simpa [kahanStep, KahanStepTrace.nextState] using
    congrArg KahanStepTrace.nextState htrace

/-- One Algorithm 4.2 step specialized to the source-facing finite
round-to-even selector of a `FloatingPointFormat`.  This is the concrete
finite-format wrapper used for result-by-result audits such as Problem 4.10. -/
noncomputable def finiteKahanStepTrace (fmt : FloatingPointFormat) (x : ℝ)
    (state : KahanState) : KahanStepTrace :=
  let temp := state.s
  let y := fmt.finiteRoundToEvenOp BasicOp.add x state.e
  let s := fmt.finiteRoundToEvenOp BasicOp.add temp y
  let e := fmt.finiteRoundToEvenOp BasicOp.add
    (fmt.finiteRoundToEvenOp BasicOp.sub temp s) y
  { temp := temp, y := y, s := s, e := e }

/-- Persistent-state update induced by one finite-format Kahan step. -/
noncomputable def finiteKahanStep (fmt : FloatingPointFormat) (x : ℝ)
    (state : KahanState) : KahanState :=
  (finiteKahanStepTrace fmt x state).nextState

/-- The `temp` assignment in Algorithm 4.2. -/
theorem kahanStepTrace_temp (fp : FPModel) (x : ℝ) (state : KahanState) :
    (kahanStepTrace fp x state).temp = state.s := by
  rfl

/-- The `y = x_i + e` assignment in Algorithm 4.2. -/
theorem kahanStepTrace_y (fp : FPModel) (x : ℝ) (state : KahanState) :
    (kahanStepTrace fp x state).y = fp.fl_add x state.e := by
  rfl

/-- The `s = temp + y` assignment in Algorithm 4.2. -/
theorem kahanStepTrace_s (fp : FPModel) (x : ℝ) (state : KahanState) :
    (kahanStepTrace fp x state).s =
      fp.fl_add (kahanStepTrace fp x state).temp
        (kahanStepTrace fp x state).y := by
  rfl

/-- The `e = (temp - s) + y` assignment in Algorithm 4.2, in the displayed
evaluation order. -/
theorem kahanStepTrace_e (fp : FPModel) (x : ℝ) (state : KahanState) :
    (kahanStepTrace fp x state).e =
      fp.fl_add
        (fp.fl_sub (kahanStepTrace fp x state).temp
          (kahanStepTrace fp x state).s)
        (kahanStepTrace fp x state).y := by
  rfl

/-- Standard-model roundoff witnesses for one Algorithm 4.2 Kahan step.

The four deltas expose the source proof's primitive operations:
`y = fl(x + e)`, `s = fl(temp + y)`, the subtraction `fl(temp - s)`,
and the final correction add `e = fl(fl(temp - s) + y)`. -/
structure KahanStepDeltaWitness (fp : FPModel) (x : ℝ) (state : KahanState) where
  deltaY : ℝ
  deltaS : ℝ
  deltaSub : ℝ
  deltaE : ℝ
  h_deltaY : |deltaY| ≤ fp.u
  h_deltaS : |deltaS| ≤ fp.u
  h_deltaSub : |deltaSub| ≤ fp.u
  h_deltaE : |deltaE| ≤ fp.u
  hy :
    (kahanStepTrace fp x state).y =
      (x + state.e) * (1 + deltaY)
  hs :
    (kahanStepTrace fp x state).s =
      ((kahanStepTrace fp x state).temp + (kahanStepTrace fp x state).y) *
        (1 + deltaS)
  hsub :
    fp.fl_sub (kahanStepTrace fp x state).temp
        (kahanStepTrace fp x state).s =
      ((kahanStepTrace fp x state).temp - (kahanStepTrace fp x state).s) *
        (1 + deltaSub)
  he :
    (kahanStepTrace fp x state).e =
      (fp.fl_sub (kahanStepTrace fp x state).temp
          (kahanStepTrace fp x state).s +
        (kahanStepTrace fp x state).y) *
        (1 + deltaE)

/-- Every abstract `FPModel` Kahan step admits the standard-model roundoff
delta witnesses used by the Knuth/Goldberg coefficient-recursion proof. -/
theorem exists_kahanStepTrace_deltaWitness
    (fp : FPModel) (x : ℝ) (state : KahanState) :
    Nonempty (KahanStepDeltaWitness fp x state) := by
  rcases fp.model_basicOp BasicOp.add x state.e (by intro h; cases h) with
    ⟨deltaY, h_deltaY, hy⟩
  rcases fp.model_basicOp BasicOp.add
      (kahanStepTrace fp x state).temp
      (kahanStepTrace fp x state).y
      (by intro h; cases h) with
    ⟨deltaS, h_deltaS, hs⟩
  rcases fp.model_basicOp BasicOp.sub
      (kahanStepTrace fp x state).temp
      (kahanStepTrace fp x state).s
      (by intro h; cases h) with
    ⟨deltaSub, h_deltaSub, hsub⟩
  rcases fp.model_basicOp BasicOp.add
      (fp.fl_sub (kahanStepTrace fp x state).temp
        (kahanStepTrace fp x state).s)
      (kahanStepTrace fp x state).y
      (by intro h; cases h) with
    ⟨deltaE, h_deltaE, he⟩
  refine
    ⟨{ deltaY := deltaY
       deltaS := deltaS
       deltaSub := deltaSub
       deltaE := deltaE
       h_deltaY := h_deltaY
       h_deltaS := h_deltaS
       h_deltaSub := h_deltaSub
       h_deltaE := h_deltaE
       hy := ?_
       hs := ?_
       hsub := ?_
       he := ?_ }⟩
  · simpa [kahanStepTrace, FPModel.round, BasicOp.exact] using hy
  · simpa [kahanStepTrace, FPModel.round, BasicOp.exact] using hs
  · simpa [FPModel.round, BasicOp.exact] using hsub
  · simpa [kahanStepTrace, FPModel.round, BasicOp.exact] using he

/-- A convenient chosen bundle of the per-operation Kahan roundoff witnesses. -/
noncomputable def kahanStepTrace_deltaWitness
    (fp : FPModel) (x : ℝ) (state : KahanState) :
    KahanStepDeltaWitness fp x state :=
  Classical.choice (exists_kahanStepTrace_deltaWitness fp x state)

/-- If the displayed correction subtraction in one Algorithm 4.2 step is
exact, choose the standard-model witness bundle with zero subtraction delta.

This is the one-step construction needed by the witness-family route for
Higham equation (4.8): exact subtraction is represented by the concrete
choice `deltaSub = 0`, while the other three operations still use the ordinary
standard-model witnesses. -/
theorem exists_kahanStepTrace_deltaWitness_of_exact_sub
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (hsubExact :
      fp.fl_sub (kahanStepTrace fp x state).temp
          (kahanStepTrace fp x state).s =
        (kahanStepTrace fp x state).temp -
          (kahanStepTrace fp x state).s) :
    ∃ w : KahanStepDeltaWitness fp x state, w.deltaSub = 0 := by
  rcases fp.model_basicOp BasicOp.add x state.e (by intro h; cases h) with
    ⟨deltaY, h_deltaY, hy⟩
  rcases fp.model_basicOp BasicOp.add
      (kahanStepTrace fp x state).temp
      (kahanStepTrace fp x state).y
      (by intro h; cases h) with
    ⟨deltaS, h_deltaS, hs⟩
  rcases fp.model_basicOp BasicOp.add
      (fp.fl_sub (kahanStepTrace fp x state).temp
        (kahanStepTrace fp x state).s)
      (kahanStepTrace fp x state).y
      (by intro h; cases h) with
    ⟨deltaE, h_deltaE, he⟩
  refine
    ⟨{ deltaY := deltaY
       deltaS := deltaS
       deltaSub := 0
       deltaE := deltaE
       h_deltaY := h_deltaY
       h_deltaS := h_deltaS
       h_deltaSub := by simpa using fp.u_nonneg
       h_deltaE := h_deltaE
       hy := ?_
       hs := ?_
       hsub := ?_
       he := ?_ }, rfl⟩
  · simpa [kahanStepTrace, FPModel.round, BasicOp.exact] using hy
  · simpa [kahanStepTrace, FPModel.round, BasicOp.exact] using hs
  · simp [hsubExact]
  · simpa [kahanStepTrace, FPModel.round, BasicOp.exact] using he

/-- A chosen one-step Kahan witness with zero subtraction delta, under an
explicit exact-subtraction hypothesis. -/
noncomputable def kahanStepTrace_deltaWitnessOfExactSub
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (hsubExact :
      fp.fl_sub (kahanStepTrace fp x state).temp
          (kahanStepTrace fp x state).s =
        (kahanStepTrace fp x state).temp -
          (kahanStepTrace fp x state).s) :
    KahanStepDeltaWitness fp x state :=
  Classical.choose
    (exists_kahanStepTrace_deltaWitness_of_exact_sub
      fp x state hsubExact)

/-- The exact-subtraction witness selected by
`kahanStepTrace_deltaWitnessOfExactSub` has zero subtraction delta. -/
theorem kahanStepTrace_deltaWitnessOfExactSub_deltaSub
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (hsubExact :
      fp.fl_sub (kahanStepTrace fp x state).temp
          (kahanStepTrace fp x state).s =
        (kahanStepTrace fp x state).temp -
          (kahanStepTrace fp x state).s) :
    (kahanStepTrace_deltaWitnessOfExactSub fp x state hsubExact).deltaSub =
      0 :=
  Classical.choose_spec
    (exists_kahanStepTrace_deltaWitness_of_exact_sub
      fp x state hsubExact)

/-- Expanded one-step recurrence for the updated Kahan sum after substituting
the standard-model delta for the `y = fl(x + e)` operation. -/
theorem kahanStepDeltaWitness_s_expanded
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) :
    (kahanStepTrace fp x state).s =
      (state.s + (x + state.e) * (1 + w.deltaY)) *
        (1 + w.deltaS) := by
  rw [w.hs, w.hy]
  simp [kahanStepTrace]

/-- Expanded one-step recurrence for the Kahan correction after substituting
the standard-model delta for the displayed `temp - s` subtraction. -/
theorem kahanStepDeltaWitness_e_expanded
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) :
    (kahanStepTrace fp x state).e =
      (((kahanStepTrace fp x state).temp -
            (kahanStepTrace fp x state).s) *
          (1 + w.deltaSub) +
        (kahanStepTrace fp x state).y) *
        (1 + w.deltaE) := by
  rw [w.he, w.hsub]

/-- Fully expanded one-step recurrence for the Kahan correction, with the
temporary sum and `y` trace variables replaced by the previous state, input, and
standard-model deltas. -/
theorem kahanStepDeltaWitness_e_fully_expanded
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) :
    let y0 := (x + state.e) * (1 + w.deltaY)
    let s0 := (state.s + y0) * (1 + w.deltaS)
    (kahanStepTrace fp x state).e =
      ((state.s - s0) * (1 + w.deltaSub) + y0) *
        (1 + w.deltaE) := by
  dsimp
  rw [kahanStepDeltaWitness_e_expanded fp x state w]
  rw [kahanStepDeltaWitness_s_expanded fp x state w, w.hy]
  simp [kahanStepTrace]

/-- Fully expanded one-step recurrence for the compensated total `s + e`, in
terms of only the previous Kahan state, the new input, and the four
standard-model deltas. -/
theorem kahanStepDeltaWitness_total_fully_expanded
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) :
    let y0 := (x + state.e) * (1 + w.deltaY)
    let s0 := (state.s + y0) * (1 + w.deltaS)
    (kahanStepTrace fp x state).s + (kahanStepTrace fp x state).e =
      s0 + ((state.s - s0) * (1 + w.deltaSub) + y0) *
        (1 + w.deltaE) := by
  dsimp
  rw [kahanStepDeltaWitness_s_expanded fp x state w]
  rw [kahanStepDeltaWitness_e_fully_expanded fp x state w]

/-- Coefficient multiplying the previous Kahan running sum in the fully
expanded compensated-total recurrence.  It is `1 + O(u^2)` under the standard
delta bounds, which is the cancellation exploited in the Knuth/Goldberg
coefficient recursion. -/
def kahanTotalStateCoeff (deltaS deltaSub deltaE : ℝ) : ℝ :=
  (1 + deltaSub) * (1 + deltaE) +
    (1 + deltaS) * (1 - (1 + deltaSub) * (1 + deltaE))

/-- Coefficient multiplying the current exact input-plus-correction term in the
fully expanded compensated-total recurrence. -/
def kahanTotalInputCoeff
    (deltaY deltaS deltaSub deltaE : ℝ) : ℝ :=
  (1 + deltaY) *
    ((1 + deltaS) * (1 - (1 + deltaSub) * (1 + deltaE)) +
      (1 + deltaE))

/-- Residual coefficient on the retained correction when the compensated-total
recurrence is rewritten in terms of the previous compensated total `s+e`
instead of the previous stored running sum `s`.

This term is zero in exact arithmetic.  It is the precise local obstruction
that remains before the ordinary Knuth/Goldberg `mu_i` recursion can be
closed for the returned Kahan sum. -/
def kahanTotalResidualCoeff
    (deltaY deltaS deltaSub deltaE : ℝ) : ℝ :=
  kahanTotalInputCoeff deltaY deltaS deltaSub deltaE -
    kahanTotalStateCoeff deltaS deltaSub deltaE

/-- Coefficient multiplying the previous stored running sum in the fully
expanded correction recurrence for `e`. -/
def kahanCorrectionStateCoeff (deltaS deltaSub deltaE : ℝ) : ℝ :=
  -deltaS * (1 + deltaSub) * (1 + deltaE)

/-- Coefficient multiplying the current exact input-plus-correction term in
the fully expanded correction recurrence for `e`. -/
def kahanCorrectionInputCoeff
    (deltaY deltaS deltaSub deltaE : ℝ) : ℝ :=
  -(1 + deltaY) * (deltaSub + deltaS * (1 + deltaSub)) *
    (1 + deltaE)

/-- Coefficient multiplying the previous stored sum in the directly expanded
stored-sum recurrence.

Unlike the compensated-total old-state coefficient, this coefficient has a
first-order term.  It is recorded separately because the final Knuth/Goldberg
route for the returned `s` must preserve cancellation with the retained
correction rather than bound the final correction as an independent residual. -/
def kahanStoredSumStateCoeff (deltaS : ℝ) : ℝ :=
  1 + deltaS

/-- Coefficient multiplying both the current input and the previous retained
correction in the directly expanded stored-sum recurrence. -/
def kahanStoredSumInputCoeff (deltaY deltaS : ℝ) : ℝ :=
  (1 + deltaY) * (1 + deltaS)

/-- The direct stored-sum current-input coefficient differs from the direct
old-stored-sum coefficient by the first input-roundoff factor. -/
theorem kahanStoredSumInputCoeff_sub_stateCoeff_eq
    (deltaY deltaS : ℝ) :
    kahanStoredSumInputCoeff deltaY deltaS -
      kahanStoredSumStateCoeff deltaS = deltaY * (1 + deltaS) := by
  dsimp [kahanStoredSumInputCoeff, kahanStoredSumStateCoeff]
  ring

/-- One-step coefficient form of the fully expanded Kahan correction
recurrence. -/
theorem kahanStepDeltaWitness_e_coefficients
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) :
    (kahanStepTrace fp x state).e =
      state.s * kahanCorrectionStateCoeff w.deltaS w.deltaSub w.deltaE +
        (x + state.e) *
          kahanCorrectionInputCoeff
            w.deltaY w.deltaS w.deltaSub w.deltaE := by
  rw [kahanStepDeltaWitness_e_fully_expanded fp x state w]
  dsimp [kahanCorrectionStateCoeff, kahanCorrectionInputCoeff]
  ring

/-- One-step coefficient form of the directly expanded Kahan stored-sum
recurrence.

This is the first cancellation-preserving returned-sum surface for the
ordinary Kahan bound: the previous retained correction is still explicit and
shares the same local coefficient as the current input. -/
theorem kahanStepDeltaWitness_s_coefficients
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) :
    (kahanStepTrace fp x state).s =
      state.s * kahanStoredSumStateCoeff w.deltaS +
        x * kahanStoredSumInputCoeff w.deltaY w.deltaS +
        state.e * kahanStoredSumInputCoeff w.deltaY w.deltaS := by
  rw [kahanStepDeltaWitness_s_expanded fp x state w]
  dsimp [kahanStoredSumStateCoeff, kahanStoredSumInputCoeff]
  ring

/-- Exact first/second-order expansion of the direct stored-sum current-input
coefficient. -/
theorem kahanStoredSumInputCoeff_sub_one_eq
    (deltaY deltaS : ℝ) :
    kahanStoredSumInputCoeff deltaY deltaS - 1 =
      deltaY + deltaS + deltaY * deltaS := by
  dsimp [kahanStoredSumInputCoeff]
  ring

/-- Local radius for the old stored-sum coefficient in the direct stored-sum
recurrence. -/
theorem kahanStoredSumStateCoeff_abs_sub_one_le
    {deltaS u : ℝ} (hS : |deltaS| ≤ u) :
    |kahanStoredSumStateCoeff deltaS - 1| ≤ u := by
  simpa [kahanStoredSumStateCoeff] using hS

/-- Local radius for the current-input coefficient in the direct stored-sum
recurrence. -/
theorem kahanStoredSumInputCoeff_abs_sub_one_le_two_u_plus_u_sq
    {deltaY deltaS u : ℝ} (hu : 0 ≤ u)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u) :
    |kahanStoredSumInputCoeff deltaY deltaS - 1| ≤
      2 * u + u ^ 2 := by
  have hYS : |deltaY * deltaS| ≤ u * u := by
    rw [abs_mul]
    exact mul_le_mul hY hS (abs_nonneg _) hu
  rw [kahanStoredSumInputCoeff_sub_one_eq]
  calc
    |deltaY + deltaS + deltaY * deltaS|
        ≤ |deltaY| + |deltaS| + |deltaY * deltaS| := by
          calc
            |deltaY + deltaS + deltaY * deltaS|
                = |(deltaY + deltaS) + deltaY * deltaS| := by ring
            _ ≤ |deltaY + deltaS| + |deltaY * deltaS| := abs_add_le _ _
            _ ≤ |deltaY| + |deltaS| + |deltaY * deltaS| := by
              nlinarith [abs_add_le deltaY deltaS]
    _ ≤ u + u + u * u := by
      nlinarith [hY, hS, hYS]
    _ = 2 * u + u ^ 2 := by ring

/-- Local radius for the gap between the direct stored-sum input and state
coefficients.  This is the coefficient multiplying the retained correction
when the returned stored sum is propagated in paired `(s+e,e)` coordinates. -/
theorem kahanStoredSumInputCoeff_sub_stateCoeff_abs_le_u_mul_one_add_u
    {deltaY deltaS u : ℝ} (hu : 0 ≤ u)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u) :
    |kahanStoredSumInputCoeff deltaY deltaS -
        kahanStoredSumStateCoeff deltaS| ≤
      u * (1 + u) := by
  rw [kahanStoredSumInputCoeff_sub_stateCoeff_eq, abs_mul]
  have hone : |1 + deltaS| ≤ 1 + u := by
    calc
      |1 + deltaS| = |deltaS + 1| := by ring_nf
      _ ≤ |deltaS| + |(1 : ℝ)| := abs_add_le deltaS 1
      _ ≤ u + 1 := by
        exact add_le_add hS (by norm_num : |(1 : ℝ)| ≤ 1)
      _ = 1 + u := by ring
  exact mul_le_mul hY hone (abs_nonneg _) (by nlinarith [hu])

/-- Exact second-order expansion of the previous-running-sum coefficient in
the Kahan compensated-total recurrence. -/
theorem kahanTotalStateCoeff_eq_one_sub_second_order
    (deltaS deltaSub deltaE : ℝ) :
    kahanTotalStateCoeff deltaS deltaSub deltaE =
      1 - deltaS * deltaSub - deltaS * deltaE -
        deltaS * deltaSub * deltaE := by
  dsimp [kahanTotalStateCoeff]
  ring

/-- Exact first/second-order expansion of the current-input coefficient in the
Kahan compensated-total recurrence.  The first-order part is
`deltaY - deltaSub`, which is the local algebra behind the `2*u + O(u^2)`
coefficient radius. -/
theorem kahanTotalInputCoeff_eq_first_second_order
    (deltaY deltaS deltaSub deltaE : ℝ) :
    kahanTotalInputCoeff deltaY deltaS deltaSub deltaE =
      1 + deltaY - deltaSub -
        deltaSub * deltaE - deltaS * deltaSub - deltaS * deltaE -
        deltaS * deltaSub * deltaE -
        deltaY * deltaSub - deltaY * deltaSub * deltaE -
        deltaY * deltaS * deltaSub - deltaY * deltaS * deltaE -
        deltaY * deltaS * deltaSub * deltaE := by
  dsimp [kahanTotalInputCoeff]
  ring

/-- Factorized error form of the current-input coefficient. -/
theorem kahanTotalInputCoeff_sub_one_eq
    (deltaY deltaS deltaSub deltaE : ℝ) :
    kahanTotalInputCoeff deltaY deltaS deltaSub deltaE - 1 =
      deltaY -
        (1 + deltaY) *
          (deltaSub + deltaSub * deltaE + deltaS * deltaSub +
            deltaS * deltaE + deltaS * deltaSub * deltaE) := by
  dsimp [kahanTotalInputCoeff]
  ring

/-- The previous-running-sum coefficient differs from `1` only by
second-order terms in the Kahan step deltas. -/
theorem kahanTotalStateCoeff_abs_sub_one_le
    {deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u)
    (hS : |deltaS| ≤ u) (hSub : |deltaSub| ≤ u)
    (hE : |deltaE| ≤ u) :
    |kahanTotalStateCoeff deltaS deltaSub deltaE - 1| ≤
      2 * u ^ 2 + u ^ 3 := by
  have hSSub : |deltaS * deltaSub| ≤ u * u := by
    rw [abs_mul]
    exact mul_le_mul hS hSub (abs_nonneg _) hu
  have hSE : |deltaS * deltaE| ≤ u * u := by
    rw [abs_mul]
    exact mul_le_mul hS hE (abs_nonneg _) hu
  have hSSubE : |deltaS * deltaSub * deltaE| ≤ u * u * u := by
    rw [abs_mul, abs_mul]
    have hprod : |deltaS| * |deltaSub| ≤ u * u :=
      mul_le_mul hS hSub (abs_nonneg _) hu
    exact mul_le_mul hprod hE (abs_nonneg _)
      (mul_nonneg hu hu)
  have hexp :
      kahanTotalStateCoeff deltaS deltaSub deltaE - 1 =
        -(deltaS * deltaSub + deltaS * deltaE +
          deltaS * deltaSub * deltaE) := by
    rw [kahanTotalStateCoeff_eq_one_sub_second_order]
    ring
  rw [hexp, abs_neg]
  calc
    |deltaS * deltaSub + deltaS * deltaE +
        deltaS * deltaSub * deltaE|
        ≤ |deltaS * deltaSub| + |deltaS * deltaE| +
            |deltaS * deltaSub * deltaE| := by
          calc
            |deltaS * deltaSub + deltaS * deltaE +
                deltaS * deltaSub * deltaE|
                = |(deltaS * deltaSub + deltaS * deltaE) +
                    deltaS * deltaSub * deltaE| := by ring
            _ ≤ |deltaS * deltaSub + deltaS * deltaE| +
                  |deltaS * deltaSub * deltaE| := abs_add_le _ _
            _ ≤ |deltaS * deltaSub| + |deltaS * deltaE| +
                  |deltaS * deltaSub * deltaE| := by
                nlinarith [abs_add_le (deltaS * deltaSub) (deltaS * deltaE)]
    _ ≤ u * u + u * u + u * u * u := by
          nlinarith [hSSub, hSE, hSSubE]
    _ = 2 * u ^ 2 + u ^ 3 := by ring

/-- The current-input coefficient has local radius
`2*u + 4*u^2 + 4*u^3 + u^4` under the four standard-model delta bounds. -/
theorem kahanTotalInputCoeff_abs_sub_one_le
    {deltaY deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u)
    (hSub : |deltaSub| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanTotalInputCoeff deltaY deltaS deltaSub deltaE - 1| ≤
      2 * u + 4 * u ^ 2 + 4 * u ^ 3 + u ^ 4 := by
  let q := deltaSub + deltaSub * deltaE + deltaS * deltaSub +
    deltaS * deltaE + deltaS * deltaSub * deltaE
  have hSubE : |deltaSub * deltaE| ≤ u * u := by
    rw [abs_mul]
    exact mul_le_mul hSub hE (abs_nonneg _) hu
  have hSSub : |deltaS * deltaSub| ≤ u * u := by
    rw [abs_mul]
    exact mul_le_mul hS hSub (abs_nonneg _) hu
  have hSE : |deltaS * deltaE| ≤ u * u := by
    rw [abs_mul]
    exact mul_le_mul hS hE (abs_nonneg _) hu
  have hSSubE : |deltaS * deltaSub * deltaE| ≤ u * u * u := by
    rw [abs_mul, abs_mul]
    have hprod : |deltaS| * |deltaSub| ≤ u * u :=
      mul_le_mul hS hSub (abs_nonneg _) hu
    exact mul_le_mul hprod hE (abs_nonneg _)
      (mul_nonneg hu hu)
  have hq : |q| ≤ u + 3 * u ^ 2 + u ^ 3 := by
    have htri :
        |q| ≤ |deltaSub| + |deltaSub * deltaE| +
            |deltaS * deltaSub| + |deltaS * deltaE| +
            |deltaS * deltaSub * deltaE| := by
      dsimp [q]
      calc
        |deltaSub + deltaSub * deltaE + deltaS * deltaSub +
            deltaS * deltaE + deltaS * deltaSub * deltaE|
            = |(((deltaSub + deltaSub * deltaE) +
                  deltaS * deltaSub) + deltaS * deltaE) +
                  deltaS * deltaSub * deltaE| := by ring
        _ ≤ |((deltaSub + deltaSub * deltaE) +
                deltaS * deltaSub) + deltaS * deltaE| +
              |deltaS * deltaSub * deltaE| := abs_add_le _ _
        _ ≤ |(deltaSub + deltaSub * deltaE) + deltaS * deltaSub| +
              |deltaS * deltaE| + |deltaS * deltaSub * deltaE| := by
            nlinarith [abs_add_le ((deltaSub + deltaSub * deltaE) +
              deltaS * deltaSub) (deltaS * deltaE)]
        _ ≤ |deltaSub + deltaSub * deltaE| +
              |deltaS * deltaSub| + |deltaS * deltaE| +
              |deltaS * deltaSub * deltaE| := by
            nlinarith [abs_add_le (deltaSub + deltaSub * deltaE)
              (deltaS * deltaSub)]
        _ ≤ |deltaSub| + |deltaSub * deltaE| +
              |deltaS * deltaSub| + |deltaS * deltaE| +
              |deltaS * deltaSub * deltaE| := by
            nlinarith [abs_add_le deltaSub (deltaSub * deltaE)]
    calc
      |q| ≤ |deltaSub| + |deltaSub * deltaE| +
          |deltaS * deltaSub| + |deltaS * deltaE| +
          |deltaS * deltaSub * deltaE| := htri
      _ ≤ u + u * u + u * u + u * u + u * u * u := by
          nlinarith [hSub, hSubE, hSSub, hSE, hSSubE]
      _ = u + 3 * u ^ 2 + u ^ 3 := by ring
  have hone :
      |1 + deltaY| ≤ 1 + u := by
    calc
      |1 + deltaY| ≤ |(1 : ℝ)| + |deltaY| := abs_add_le _ _
      _ = 1 + |deltaY| := by norm_num
      _ ≤ 1 + u := by nlinarith [hY]
  have hprod :
      |(1 + deltaY) * q| ≤ (1 + u) * (u + 3 * u ^ 2 + u ^ 3) := by
    rw [abs_mul]
    exact mul_le_mul hone hq (abs_nonneg _) (by nlinarith [hu])
  have hexp :
      kahanTotalInputCoeff deltaY deltaS deltaSub deltaE - 1 =
        deltaY - (1 + deltaY) * q := by
    dsimp [q]
    exact kahanTotalInputCoeff_sub_one_eq deltaY deltaS deltaSub deltaE
  rw [hexp]
  calc
    |deltaY - (1 + deltaY) * q|
        ≤ |deltaY| + |(1 + deltaY) * q| := by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_add_le deltaY (-((1 + deltaY) * q))
    _ ≤ u + (1 + u) * (u + 3 * u ^ 2 + u ^ 3) := by
          nlinarith [hY, hprod]
    _ = 2 * u + 4 * u ^ 2 + 4 * u ^ 3 + u ^ 4 := by ring

/-- Readable small-`u` version of the old-state coefficient bound. -/
theorem kahanTotalStateCoeff_abs_sub_one_le_three_u_sq
    {deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hS : |deltaS| ≤ u) (hSub : |deltaSub| ≤ u)
    (hE : |deltaE| ≤ u) :
    |kahanTotalStateCoeff deltaS deltaSub deltaE - 1| ≤
      3 * u ^ 2 := by
  have hbase :=
    kahanTotalStateCoeff_abs_sub_one_le
      (deltaS := deltaS) (deltaSub := deltaSub) (deltaE := deltaE)
      (u := u) hu hS hSub hE
  have hu3_le_u2 : u ^ 3 ≤ u ^ 2 := by
    have h :=
      mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)
    nlinarith
  nlinarith

/-- Readable small-`u` version of the current-input coefficient bound. -/
theorem kahanTotalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
    {deltaY deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u)
    (hSub : |deltaSub| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanTotalInputCoeff deltaY deltaS deltaSub deltaE - 1| ≤
      2 * u + 9 * u ^ 2 := by
  have hbase :=
    kahanTotalInputCoeff_abs_sub_one_le
      (deltaY := deltaY) (deltaS := deltaS) (deltaSub := deltaSub)
      (deltaE := deltaE) (u := u) hu hY hS hSub hE
  have hu3_le_u2 : u ^ 3 ≤ u ^ 2 := by
    have h :=
      mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)
    nlinarith
  have hu2_le_one : u ^ 2 ≤ 1 := by
    have h :=
      mul_le_mul hu1 hu1 hu (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hu4_le_u2 : u ^ 4 ≤ u ^ 2 := by
    have h :=
      mul_le_mul_of_nonneg_left hu2_le_one (sq_nonneg u)
    nlinarith
  nlinarith

/-- Source-shaped nonempty-horizon version of the current-input coefficient
radius, useful before the all-prefix Goldberg/Knuth product collapse. -/
theorem kahanTotalInputCoeff_abs_sub_one_le_two_u_plus_nine_n_u_sq
    {deltaY deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    {n : ℕ} (hn : 1 ≤ n)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u)
    (hSub : |deltaSub| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanTotalInputCoeff deltaY deltaS deltaSub deltaE - 1| ≤
      2 * u + 9 * (n : ℝ) * u ^ 2 := by
  have hlocal :=
    kahanTotalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
      (deltaY := deltaY) (deltaS := deltaS) (deltaSub := deltaSub)
      (deltaE := deltaE) (u := u) hu hu1 hY hS hSub hE
  have hn_real : (1 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hscale : 9 * u ^ 2 ≤ (n : ℝ) * (9 * u ^ 2) :=
    le_mul_of_one_le_left
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) (sq_nonneg u))
      hn_real
  have hscale' : 9 * u ^ 2 ≤ 9 * (n : ℝ) * u ^ 2 := by
    calc
      9 * u ^ 2 ≤ (n : ℝ) * (9 * u ^ 2) := hscale
      _ = 9 * (n : ℝ) * u ^ 2 := by ring
  nlinarith

/-- Small-`u` local bound for the retained-correction residual coefficient. -/
theorem kahanTotalResidualCoeff_abs_le_two_u_plus_twelve_u_sq
    {deltaY deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u)
    (hSub : |deltaSub| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE| ≤
      2 * u + 12 * u ^ 2 := by
  let A := kahanTotalStateCoeff deltaS deltaSub deltaE
  let B := kahanTotalInputCoeff deltaY deltaS deltaSub deltaE
  have hA : |A - 1| ≤ 3 * u ^ 2 := by
    simpa [A] using
      kahanTotalStateCoeff_abs_sub_one_le_three_u_sq
        (deltaS := deltaS) (deltaSub := deltaSub) (deltaE := deltaE)
        (u := u) hu hu1 hS hSub hE
  have hB : |B - 1| ≤ 2 * u + 9 * u ^ 2 := by
    simpa [B] using
      kahanTotalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
        (deltaY := deltaY) (deltaS := deltaS) (deltaSub := deltaSub)
        (deltaE := deltaE) (u := u) hu hu1 hY hS hSub hE
  have htri : |B - A| ≤ |B - 1| + |A - 1| := by
    have hrewrite : B - A = (B - 1) + (1 - A) := by ring
    rw [hrewrite]
    calc
      |(B - 1) + (1 - A)| ≤ |B - 1| + |1 - A| :=
        abs_add_le (B - 1) (1 - A)
      _ = |B - 1| + |A - 1| := by
        rw [abs_sub_comm 1 A]
  have hres :
      |kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE| = |B - A| := by
    rfl
  rw [hres]
  nlinarith

/-- Source-shaped nonempty-horizon wrapper for the retained-correction
residual coefficient. -/
theorem kahanTotalResidualCoeff_abs_le_two_u_plus_twelve_n_u_sq
    {deltaY deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    {n : ℕ} (hn : 1 ≤ n)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u)
    (hSub : |deltaSub| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE| ≤
      2 * u + 12 * (n : ℝ) * u ^ 2 := by
  have hlocal :=
    kahanTotalResidualCoeff_abs_le_two_u_plus_twelve_u_sq
      (deltaY := deltaY) (deltaS := deltaS) (deltaSub := deltaSub)
      (deltaE := deltaE) (u := u) hu hu1 hY hS hSub hE
  have hn_real : (1 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hscale : 12 * u ^ 2 ≤ (n : ℝ) * (12 * u ^ 2) :=
    le_mul_of_one_le_left
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) (sq_nonneg u))
      hn_real
  have hscale' : 12 * u ^ 2 ≤ 12 * (n : ℝ) * u ^ 2 := by
    calc
      12 * u ^ 2 ≤ (n : ℝ) * (12 * u ^ 2) := hscale
      _ = 12 * (n : ℝ) * u ^ 2 := by ring
  nlinarith

/-- Local bound for the previous-running-sum coefficient in the fully expanded
Kahan correction recurrence. -/
theorem kahanCorrectionStateCoeff_abs_le
    {deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u)
    (hS : |deltaS| ≤ u) (hSub : |deltaSub| ≤ u)
    (hE : |deltaE| ≤ u) :
    |kahanCorrectionStateCoeff deltaS deltaSub deltaE| ≤
      u * (1 + u) ^ 2 := by
  have hSub1 : |1 + deltaSub| ≤ 1 + u := by
    calc
      |1 + deltaSub| ≤ |(1 : ℝ)| + |deltaSub| := abs_add_le _ _
      _ = 1 + |deltaSub| := by norm_num
      _ ≤ 1 + u := by nlinarith [hSub]
  have hE1 : |1 + deltaE| ≤ 1 + u := by
    calc
      |1 + deltaE| ≤ |(1 : ℝ)| + |deltaE| := abs_add_le _ _
      _ = 1 + |deltaE| := by norm_num
      _ ≤ 1 + u := by nlinarith [hE]
  have hprod : |deltaS| * |1 + deltaSub| ≤ u * (1 + u) := by
    exact mul_le_mul hS hSub1 (abs_nonneg _) hu
  rw [kahanCorrectionStateCoeff, abs_mul, abs_mul, abs_neg]
  calc
    |deltaS| * |1 + deltaSub| * |1 + deltaE|
        ≤ (u * (1 + u)) * (1 + u) := by
          exact mul_le_mul hprod hE1 (abs_nonneg _)
            (mul_nonneg hu (by nlinarith [hu]))
    _ = u * (1 + u) ^ 2 := by ring

/-- Local bound for the current input-plus-correction coefficient in the fully
expanded Kahan correction recurrence. -/
theorem kahanCorrectionInputCoeff_abs_le
    {deltaY deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u)
    (hSub : |deltaSub| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanCorrectionInputCoeff deltaY deltaS deltaSub deltaE| ≤
      u * (1 + u) ^ 2 * (2 + u) := by
  have hY1 : |1 + deltaY| ≤ 1 + u := by
    calc
      |1 + deltaY| ≤ |(1 : ℝ)| + |deltaY| := abs_add_le _ _
      _ = 1 + |deltaY| := by norm_num
      _ ≤ 1 + u := by nlinarith [hY]
  have hSub1 : |1 + deltaSub| ≤ 1 + u := by
    calc
      |1 + deltaSub| ≤ |(1 : ℝ)| + |deltaSub| := abs_add_le _ _
      _ = 1 + |deltaSub| := by norm_num
      _ ≤ 1 + u := by nlinarith [hSub]
  have hE1 : |1 + deltaE| ≤ 1 + u := by
    calc
      |1 + deltaE| ≤ |(1 : ℝ)| + |deltaE| := abs_add_le _ _
      _ = 1 + |deltaE| := by norm_num
      _ ≤ 1 + u := by nlinarith [hE]
  have hSprod : |deltaS * (1 + deltaSub)| ≤ u * (1 + u) := by
    rw [abs_mul]
    exact mul_le_mul hS hSub1 (abs_nonneg _) hu
  have hq : |deltaSub + deltaS * (1 + deltaSub)| ≤ u * (2 + u) := by
    calc
      |deltaSub + deltaS * (1 + deltaSub)|
          ≤ |deltaSub| + |deltaS * (1 + deltaSub)| := abs_add_le _ _
      _ ≤ u + u * (1 + u) := by nlinarith [hSub, hSprod]
      _ = u * (2 + u) := by ring
  rw [kahanCorrectionInputCoeff, abs_mul, abs_mul, abs_neg]
  calc
    |1 + deltaY| * |deltaSub + deltaS * (1 + deltaSub)| *
        |1 + deltaE|
        ≤ (1 + u) * (u * (2 + u)) * (1 + u) := by
          exact mul_le_mul
            (mul_le_mul hY1 hq (abs_nonneg _) (by nlinarith [hu]))
            hE1 (abs_nonneg _)
            (mul_nonneg (by nlinarith [hu])
              (mul_nonneg hu (by nlinarith [hu])))
    _ = u * (1 + u) ^ 2 * (2 + u) := by ring

/-! ### General correction-subtraction cancellation

The exact-subtraction route below sets `deltaSub = 0`.  The ordinary
Goldberg/Higham recurrence instead has to keep `deltaSub`, but it appears with
opposite signs in the stored sum and retained correction rows.  These lemmas
isolate that local cancellation before any suffix product argument is applied.
-/

/-- The paired correction residual is `-deltaSub` plus only higher-order
terms in the four local Kahan roundoff deltas. -/
theorem kahanCorrectionInputCoeff_sub_stateCoeff_add_deltaSub_eq
    (deltaY deltaS deltaSub deltaE : ℝ) :
    kahanCorrectionInputCoeff deltaY deltaS deltaSub deltaE -
        kahanCorrectionStateCoeff deltaS deltaSub deltaE + deltaSub =
      -(deltaSub * deltaE + deltaY * deltaSub +
        deltaY * deltaSub * deltaE + deltaY * deltaS +
        deltaY * deltaS * deltaE + deltaY * deltaS * deltaSub +
        deltaY * deltaS * deltaSub * deltaE) := by
  dsimp [kahanCorrectionInputCoeff, kahanCorrectionStateCoeff]
  ring

/-- Small-`u` bound for the higher-order remainder in the general correction
residual cancellation. -/
theorem kahanCorrectionInputCoeff_sub_stateCoeff_add_deltaSub_abs_le_seven_u_sq
    {deltaY deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u)
    (hSub : |deltaSub| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanCorrectionInputCoeff deltaY deltaS deltaSub deltaE -
        kahanCorrectionStateCoeff deltaS deltaSub deltaE + deltaSub| ≤
      7 * u ^ 2 := by
  let a := deltaSub * deltaE
  let b := deltaY * deltaSub
  let c := deltaY * deltaSub * deltaE
  let d := deltaY * deltaS
  let e := deltaY * deltaS * deltaE
  let f := deltaY * deltaS * deltaSub
  let g := deltaY * deltaS * deltaSub * deltaE
  have ha : |a| ≤ u ^ 2 := by
    dsimp [a]
    calc
      |deltaSub * deltaE| = |deltaSub| * |deltaE| := by rw [abs_mul]
      _ ≤ u * u := mul_le_mul hSub hE (abs_nonneg _) hu
      _ = u ^ 2 := by ring
  have hb : |b| ≤ u ^ 2 := by
    dsimp [b]
    calc
      |deltaY * deltaSub| = |deltaY| * |deltaSub| := by rw [abs_mul]
      _ ≤ u * u := mul_le_mul hY hSub (abs_nonneg _) hu
      _ = u ^ 2 := by ring
  have hc : |c| ≤ u ^ 3 := by
    dsimp [c]
    calc
      |deltaY * deltaSub * deltaE| =
          |deltaY| * |deltaSub| * |deltaE| := by rw [abs_mul, abs_mul]
      _ ≤ u * u * u := by
          have hprod : |deltaY| * |deltaSub| ≤ u * u :=
            mul_le_mul hY hSub (abs_nonneg _) hu
          exact mul_le_mul hprod hE (abs_nonneg _)
            (mul_nonneg hu hu)
      _ = u ^ 3 := by ring
  have hd : |d| ≤ u ^ 2 := by
    dsimp [d]
    calc
      |deltaY * deltaS| = |deltaY| * |deltaS| := by rw [abs_mul]
      _ ≤ u * u := mul_le_mul hY hS (abs_nonneg _) hu
      _ = u ^ 2 := by ring
  have he : |e| ≤ u ^ 3 := by
    dsimp [e]
    calc
      |deltaY * deltaS * deltaE| =
          |deltaY| * |deltaS| * |deltaE| := by rw [abs_mul, abs_mul]
      _ ≤ u * u * u := by
          have hprod : |deltaY| * |deltaS| ≤ u * u :=
            mul_le_mul hY hS (abs_nonneg _) hu
          exact mul_le_mul hprod hE (abs_nonneg _)
            (mul_nonneg hu hu)
      _ = u ^ 3 := by ring
  have hf : |f| ≤ u ^ 3 := by
    dsimp [f]
    calc
      |deltaY * deltaS * deltaSub| =
          |deltaY| * |deltaS| * |deltaSub| := by rw [abs_mul, abs_mul]
      _ ≤ u * u * u := by
          have hprod : |deltaY| * |deltaS| ≤ u * u :=
            mul_le_mul hY hS (abs_nonneg _) hu
          exact mul_le_mul hprod hSub (abs_nonneg _)
            (mul_nonneg hu hu)
      _ = u ^ 3 := by ring
  have hg : |g| ≤ u ^ 4 := by
    dsimp [g]
    calc
      |deltaY * deltaS * deltaSub * deltaE| =
          |deltaY| * |deltaS| * |deltaSub| * |deltaE| := by
            rw [abs_mul, abs_mul, abs_mul]
      _ ≤ u * u * u * u := by
          have hYS : |deltaY| * |deltaS| ≤ u * u :=
            mul_le_mul hY hS (abs_nonneg _) hu
          have hYSSub :
              |deltaY| * |deltaS| * |deltaSub| ≤ u * u * u :=
            mul_le_mul hYS hSub (abs_nonneg _)
              (mul_nonneg hu hu)
          exact mul_le_mul hYSSub hE (abs_nonneg _)
            (mul_nonneg (mul_nonneg hu hu) hu)
      _ = u ^ 4 := by ring
  have htri :
      |a + b + c + d + e + f + g| ≤
        |a| + |b| + |c| + |d| + |e| + |f| + |g| := by
    calc
      |a + b + c + d + e + f + g|
          = |((((a + b) + c) + d) + e) + f + g| := by ring
      _ ≤ |((((a + b) + c) + d) + e) + f| + |g| :=
        abs_add_le _ _
      _ ≤ |(((a + b) + c) + d) + e| + |f| + |g| := by
        nlinarith [abs_add_le ((((a + b) + c) + d) + e) f]
      _ ≤ |((a + b) + c) + d| + |e| + |f| + |g| := by
        nlinarith [abs_add_le (((a + b) + c) + d) e]
      _ ≤ |(a + b) + c| + |d| + |e| + |f| + |g| := by
        nlinarith [abs_add_le ((a + b) + c) d]
      _ ≤ |a + b| + |c| + |d| + |e| + |f| + |g| := by
        nlinarith [abs_add_le (a + b) c]
      _ ≤ |a| + |b| + |c| + |d| + |e| + |f| + |g| := by
        nlinarith [abs_add_le a b]
  have hu3_le_u2 : u ^ 3 ≤ u ^ 2 := by
    have h :=
      mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)
    nlinarith
  have hu2_le_one : u ^ 2 ≤ 1 := by
    have h :=
      mul_le_mul hu1 hu1 hu (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hu4_le_u2 : u ^ 4 ≤ u ^ 2 := by
    have h :=
      mul_le_mul_of_nonneg_left hu2_le_one (sq_nonneg u)
    nlinarith
  rw [kahanCorrectionInputCoeff_sub_stateCoeff_add_deltaSub_eq, abs_neg]
  have hsum :
      |deltaSub * deltaE + deltaY * deltaSub +
          deltaY * deltaSub * deltaE + deltaY * deltaS +
          deltaY * deltaS * deltaE + deltaY * deltaS * deltaSub +
          deltaY * deltaS * deltaSub * deltaE| ≤
        |a| + |b| + |c| + |d| + |e| + |f| + |g| := by
    simpa [a, b, c, d, e, f, g] using htri
  calc
    |deltaSub * deltaE + deltaY * deltaSub +
        deltaY * deltaSub * deltaE + deltaY * deltaS +
        deltaY * deltaS * deltaE + deltaY * deltaS * deltaSub +
        deltaY * deltaS * deltaSub * deltaE|
        ≤ |a| + |b| + |c| + |d| + |e| + |f| + |g| := hsum
    _ ≤ u ^ 2 + u ^ 2 + u ^ 3 + u ^ 2 + u ^ 3 + u ^ 3 +
          u ^ 4 := by
        nlinarith [ha, hb, hc, hd, he, hf, hg]
    _ ≤ 7 * u ^ 2 := by
        nlinarith [hu3_le_u2, hu4_le_u2]

/-- The difference between the paired-total residual and the correction
residual has first-order part `deltaY`. -/
theorem kahanTotalResidualCoeff_sub_correctionResidualCoeff_sub_deltaY_eq
    (deltaY deltaS deltaSub deltaE : ℝ) :
    kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE -
        (kahanCorrectionInputCoeff deltaY deltaS deltaSub deltaE -
          kahanCorrectionStateCoeff deltaS deltaSub deltaE) - deltaY =
      deltaY * deltaS := by
  dsimp [kahanTotalResidualCoeff, kahanTotalInputCoeff,
    kahanTotalStateCoeff, kahanCorrectionInputCoeff,
    kahanCorrectionStateCoeff]
  ring

/-- Small-`u` bound for the higher-order remainder in
`totalResidual - correctionResidual = deltaY + O(u^2)`. -/
theorem kahanTotalResidualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq
    {deltaY deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u) :
    |kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE -
        (kahanCorrectionInputCoeff deltaY deltaS deltaSub deltaE -
          kahanCorrectionStateCoeff deltaS deltaSub deltaE) - deltaY| ≤
      u ^ 2 := by
  rw [kahanTotalResidualCoeff_sub_correctionResidualCoeff_sub_deltaY_eq]
  calc
    |deltaY * deltaS| = |deltaY| * |deltaS| := by rw [abs_mul]
    _ ≤ u * u := mul_le_mul hY hS (abs_nonneg _) hu
    _ = u ^ 2 := by ring

/-- Combined local residual cancellation: the paired-total residual has
first-order part `deltaY - deltaSub`; all remaining terms are second order. -/
theorem kahanTotalResidualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq
    {deltaY deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u)
    (hSub : |deltaSub| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE +
        deltaSub - deltaY| ≤
      8 * u ^ 2 := by
  let correctionResidual :=
    kahanCorrectionInputCoeff deltaY deltaS deltaSub deltaE -
      kahanCorrectionStateCoeff deltaS deltaSub deltaE
  have htotal :
      |kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE -
          correctionResidual - deltaY| ≤ u ^ 2 := by
    simpa [correctionResidual] using
      kahanTotalResidualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq
        (deltaY := deltaY) (deltaS := deltaS) (deltaSub := deltaSub)
        (deltaE := deltaE) (u := u) hu hY hS
  have hcorr :
      |correctionResidual + deltaSub| ≤ 7 * u ^ 2 := by
    simpa [correctionResidual] using
      kahanCorrectionInputCoeff_sub_stateCoeff_add_deltaSub_abs_le_seven_u_sq
        (deltaY := deltaY) (deltaS := deltaS) (deltaSub := deltaSub)
        (deltaE := deltaE) (u := u) hu hu1 hY hS hSub hE
  have hrewrite :
      kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE +
          deltaSub - deltaY =
        (kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE -
            correctionResidual - deltaY) +
          (correctionResidual + deltaSub) := by
    ring
  rw [hrewrite]
  calc
    |(kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE -
          correctionResidual - deltaY) +
        (correctionResidual + deltaSub)|
        ≤ |kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE -
            correctionResidual - deltaY| +
          |correctionResidual + deltaSub| := abs_add_le _ _
    _ ≤ u ^ 2 + 7 * u ^ 2 := add_le_add htotal hcorr
    _ = 8 * u ^ 2 := by ring

/-! ### Exact correction-subtraction coefficient bounds

The following local lemmas isolate the algebra used by the Goldberg/Higham
route when the correction subtraction `temp - s` is exact.  Under the bare
relative-error model the chosen subtraction delta may be first order; with
`deltaSub = 0`, the paired correction residual drops to second order. -/

/-- With exact correction subtraction, the compensated-total old-state
coefficient differs from one by only `u^2`. -/
theorem kahanTotalStateCoeff_abs_sub_one_le_u_sq_of_deltaSub_zero
    {deltaS deltaE u : ℝ} (hu : 0 ≤ u)
    (hS : |deltaS| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanTotalStateCoeff deltaS 0 deltaE - 1| ≤ u ^ 2 := by
  have hSE : |deltaS * deltaE| ≤ u * u := by
    rw [abs_mul]
    exact mul_le_mul hS hE (abs_nonneg _) hu
  have hrewrite :
      kahanTotalStateCoeff deltaS 0 deltaE - 1 =
        -(deltaS * deltaE) := by
    rw [kahanTotalStateCoeff_eq_one_sub_second_order]
    ring
  rw [hrewrite, abs_neg]
  simpa [pow_two] using hSE

/-- With exact correction subtraction, the compensated-total current-input
coefficient has only one first-order term. -/
theorem kahanTotalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_deltaSub_zero
    {deltaY deltaS deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanTotalInputCoeff deltaY deltaS 0 deltaE - 1| ≤
      u + 2 * u ^ 2 := by
  have hSE : |deltaS * deltaE| ≤ u * u := by
    rw [abs_mul]
    exact mul_le_mul hS hE (abs_nonneg _) hu
  have hYSE : |deltaY * deltaS * deltaE| ≤ u * u * u := by
    rw [abs_mul, abs_mul]
    have hYS : |deltaY| * |deltaS| ≤ u * u :=
      mul_le_mul hY hS (abs_nonneg _) hu
    exact mul_le_mul hYS hE (abs_nonneg _) (mul_nonneg hu hu)
  have hu3_le_u2 : u ^ 3 ≤ u ^ 2 := by
    have h :=
      mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)
    nlinarith
  have hrewrite :
      kahanTotalInputCoeff deltaY deltaS 0 deltaE - 1 =
        deltaY - deltaS * deltaE - deltaY * deltaS * deltaE := by
    rw [kahanTotalInputCoeff_eq_first_second_order]
    ring
  rw [hrewrite]
  calc
    |deltaY - deltaS * deltaE - deltaY * deltaS * deltaE|
        ≤ |deltaY| + |deltaS * deltaE| +
            |deltaY * deltaS * deltaE| := by
          calc
            |deltaY - deltaS * deltaE - deltaY * deltaS * deltaE|
                = |(deltaY - deltaS * deltaE) -
                    deltaY * deltaS * deltaE| := by ring
            _ ≤ |deltaY - deltaS * deltaE| +
                  |deltaY * deltaS * deltaE| := by
                simpa [sub_eq_add_neg, abs_neg] using
                  abs_add_le (deltaY - deltaS * deltaE)
                    (-(deltaY * deltaS * deltaE))
            _ ≤ |deltaY| + |deltaS * deltaE| +
                  |deltaY * deltaS * deltaE| := by
                have h :
                    |deltaY - deltaS * deltaE| ≤
                      |deltaY| + |deltaS * deltaE| := by
                  simpa [sub_eq_add_neg, abs_neg] using
                  abs_add_le deltaY (-(deltaS * deltaE))
                nlinarith
    _ ≤ u + u * u + u * u * u := by
          nlinarith [hY, hSE, hYSE]
    _ ≤ u + 2 * u ^ 2 := by
          nlinarith

/-- With exact correction subtraction, the compensated-total residual
coefficient is first order only in the input-add delta. -/
theorem kahanTotalResidualCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero
    {deltaY deltaS deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanTotalResidualCoeff deltaY deltaS 0 deltaE| ≤
      u + u ^ 2 := by
  have hYSE : |deltaY * deltaS * deltaE| ≤ u * u * u := by
    rw [abs_mul, abs_mul]
    have hYS : |deltaY| * |deltaS| ≤ u * u :=
      mul_le_mul hY hS (abs_nonneg _) hu
    exact mul_le_mul hYS hE (abs_nonneg _) (mul_nonneg hu hu)
  have hu3_le_u2 : u ^ 3 ≤ u ^ 2 := by
    have h :=
      mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)
    nlinarith
  have hrewrite :
      kahanTotalResidualCoeff deltaY deltaS 0 deltaE =
        deltaY - deltaY * deltaS * deltaE := by
    dsimp [kahanTotalResidualCoeff]
    rw [kahanTotalInputCoeff_eq_first_second_order]
    rw [kahanTotalStateCoeff_eq_one_sub_second_order]
    ring
  rw [hrewrite]
  calc
    |deltaY - deltaY * deltaS * deltaE|
        ≤ |deltaY| + |deltaY * deltaS * deltaE| := by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_add_le deltaY (-(deltaY * deltaS * deltaE))
    _ ≤ u + u * u * u := by
          nlinarith [hY, hYSE]
    _ ≤ u + u ^ 2 := by
          nlinarith

/-- With exact correction subtraction, the correction old-total coefficient
has radius `u + u^2`. -/
theorem kahanCorrectionStateCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero
    {deltaS deltaE u : ℝ} (hu : 0 ≤ u)
    (hS : |deltaS| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanCorrectionStateCoeff deltaS 0 deltaE| ≤
      u + u ^ 2 := by
  have hE1 : |1 + deltaE| ≤ 1 + u := by
    calc
      |1 + deltaE| ≤ |(1 : ℝ)| + |deltaE| := abs_add_le _ _
      _ = 1 + |deltaE| := by norm_num
      _ ≤ 1 + u := by nlinarith [hE]
  rw [kahanCorrectionStateCoeff, abs_mul, abs_mul, abs_neg]
  calc
    |deltaS| * |1 + 0| * |1 + deltaE|
        ≤ u * 1 * (1 + u) := by
          have hOneZero : |(1 : ℝ) + 0| ≤ 1 := by norm_num
          exact mul_le_mul
            (mul_le_mul hS hOneZero
              (abs_nonneg _) hu)
            hE1 (abs_nonneg _)
            (mul_nonneg hu (by norm_num))
    _ = u + u ^ 2 := by ring

/-- With exact correction subtraction, the correction current-input
coefficient has radius `u + O(u^2)`. -/
theorem kahanCorrectionInputCoeff_abs_le_u_plus_three_u_sq_of_deltaSub_zero
    {deltaY deltaS deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanCorrectionInputCoeff deltaY deltaS 0 deltaE| ≤
      u + 3 * u ^ 2 := by
  have hY1 : |1 + deltaY| ≤ 1 + u := by
    calc
      |1 + deltaY| ≤ |(1 : ℝ)| + |deltaY| := abs_add_le _ _
      _ = 1 + |deltaY| := by norm_num
      _ ≤ 1 + u := by nlinarith [hY]
  have hE1 : |1 + deltaE| ≤ 1 + u := by
    calc
      |1 + deltaE| ≤ |(1 : ℝ)| + |deltaE| := abs_add_le _ _
      _ = 1 + |deltaE| := by norm_num
      _ ≤ 1 + u := by nlinarith [hE]
  have hprod :
      |1 + deltaY| * |deltaS| * |1 + deltaE| ≤
        (1 + u) * u * (1 + u) := by
    exact mul_le_mul
      (mul_le_mul hY1 hS (abs_nonneg _) (by nlinarith [hu]))
      hE1 (abs_nonneg _)
      (mul_nonneg (by nlinarith [hu]) hu)
  have hu3_le_u2 : u ^ 3 ≤ u ^ 2 := by
    have h :=
      mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)
    nlinarith
  rw [kahanCorrectionInputCoeff, abs_mul, abs_mul, abs_neg]
  calc
    |1 + deltaY| * |0 + deltaS * (1 + 0)| * |1 + deltaE|
        = |1 + deltaY| * |deltaS| * |1 + deltaE| := by ring_nf
    _ ≤ (1 + u) * u * (1 + u) := hprod
    _ = u + 2 * u ^ 2 + u ^ 3 := by ring
    _ ≤ u + 3 * u ^ 2 := by nlinarith

/-- Exact algebra for the correction residual `D - C` when the correction
subtraction has zero roundoff. -/
theorem kahanCorrectionInputCoeff_sub_stateCoeff_eq_deltaSub_zero
    (deltaY deltaS deltaE : ℝ) :
    kahanCorrectionInputCoeff deltaY deltaS 0 deltaE -
        kahanCorrectionStateCoeff deltaS 0 deltaE =
      -deltaY * deltaS * (1 + deltaE) := by
  dsimp [kahanCorrectionInputCoeff, kahanCorrectionStateCoeff]
  ring

/-- With exact correction subtraction, the paired correction residual is
second order. -/
theorem kahanCorrectionResidualCoeff_abs_le_two_u_sq_of_deltaSub_zero
    {deltaY deltaS deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanCorrectionInputCoeff deltaY deltaS 0 deltaE -
        kahanCorrectionStateCoeff deltaS 0 deltaE| ≤
      2 * u ^ 2 := by
  rw [kahanCorrectionInputCoeff_sub_stateCoeff_eq_deltaSub_zero]
  have hE1 : |1 + deltaE| ≤ 1 + u := by
    calc
      |1 + deltaE| ≤ |(1 : ℝ)| + |deltaE| := abs_add_le _ _
      _ = 1 + |deltaE| := by norm_num
      _ ≤ 1 + u := by nlinarith [hE]
  have hYS : |deltaY * deltaS| ≤ u * u := by
    rw [abs_mul]
    exact mul_le_mul hY hS (abs_nonneg _) hu
  have hprod :
      |deltaY * deltaS * (1 + deltaE)| ≤ u ^ 2 * (1 + u) := by
    rw [abs_mul]
    have hYS' : |deltaY * deltaS| ≤ u ^ 2 := by
      simpa [pow_two] using hYS
    exact mul_le_mul hYS' hE1 (abs_nonneg _) (sq_nonneg u)
  have hneg :
      |-deltaY * deltaS * (1 + deltaE)| =
        |deltaY * deltaS * (1 + deltaE)| := by
    rw [show -deltaY * deltaS * (1 + deltaE) =
        -(deltaY * deltaS * (1 + deltaE)) by ring, abs_neg]
  rw [hneg]
  calc
    |deltaY * deltaS * (1 + deltaE)| ≤ u ^ 2 * (1 + u) := hprod
    _ = u ^ 2 + u ^ 3 := by ring
    _ ≤ 2 * u ^ 2 := by
        have hu3_le_u2 : u ^ 3 ≤ u ^ 2 := by
          have h :=
            mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)
          nlinarith
        nlinarith

/-- Local absolute bound for the retained correction produced by one Kahan
step. -/
theorem kahanStepDeltaWitness_e_abs_le
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) :
    |(kahanStepTrace fp x state).e| ≤
      fp.u * (1 + fp.u) ^ 2 * |state.s| +
        fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) * |x + state.e| := by
  have hCs := kahanCorrectionStateCoeff_abs_le
    (u := fp.u) fp.u_nonneg w.h_deltaS w.h_deltaSub w.h_deltaE
  have hCx := kahanCorrectionInputCoeff_abs_le
    (u := fp.u) fp.u_nonneg w.h_deltaY w.h_deltaS w.h_deltaSub w.h_deltaE
  rw [kahanStepDeltaWitness_e_coefficients fp x state w]
  calc
    |state.s * kahanCorrectionStateCoeff w.deltaS w.deltaSub w.deltaE +
        (x + state.e) *
          kahanCorrectionInputCoeff w.deltaY w.deltaS w.deltaSub w.deltaE|
        ≤ |state.s *
              kahanCorrectionStateCoeff w.deltaS w.deltaSub w.deltaE| +
            |(x + state.e) *
              kahanCorrectionInputCoeff
                w.deltaY w.deltaS w.deltaSub w.deltaE| :=
          abs_add_le _ _
    _ = |state.s| *
          |kahanCorrectionStateCoeff w.deltaS w.deltaSub w.deltaE| +
          |x + state.e| *
            |kahanCorrectionInputCoeff
              w.deltaY w.deltaS w.deltaSub w.deltaE| := by
        rw [abs_mul, abs_mul]
    _ ≤ |state.s| * (fp.u * (1 + fp.u) ^ 2) +
          |x + state.e| *
            (fp.u * (1 + fp.u) ^ 2 * (2 + fp.u)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hCs (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hCx (abs_nonneg _))
    _ = fp.u * (1 + fp.u) ^ 2 * |state.s| +
          fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
            |x + state.e| := by
        ring

/-- Split-input version of the local absolute bound for the retained
correction produced by one Kahan step. -/
theorem kahanStepDeltaWitness_e_abs_le_split
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) :
    |(kahanStepTrace fp x state).e| ≤
      fp.u * (1 + fp.u) ^ 2 * |state.s| +
        fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
          (|x| + |state.e|) := by
  have hprev := kahanStepDeltaWitness_e_abs_le fp x state w
  have hcoef_nonneg :
      0 ≤ fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) := by
    exact mul_nonneg
      (mul_nonneg fp.u_nonneg (sq_nonneg (1 + fp.u)))
      (by nlinarith [fp.u_nonneg])
  have hmul :
      fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) * |x + state.e| ≤
        fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
          (|x| + |state.e|) := by
    exact mul_le_mul_of_nonneg_left (abs_add_le x state.e) hcoef_nonneg
  calc
    |(kahanStepTrace fp x state).e| ≤
        fp.u * (1 + fp.u) ^ 2 * |state.s| +
          fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
            |x + state.e| := hprev
    _ ≤ fp.u * (1 + fp.u) ^ 2 * |state.s| +
          fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
            (|x| + |state.e|) := by
        exact add_le_add (le_refl _) hmul

/-- One step of the residual-aware affine coefficient recurrence that remains
after the local Kahan compensated-total algebra has exposed coefficients for
the previous total, current input, and retained correction. -/
structure KahanAffineCoeffStep where
  A : ℝ
  B : ℝ
  R : ℝ
  x : ℝ
  e : ℝ

/-- Source contribution of one residual-aware affine coefficient step. -/
def KahanAffineCoeffStep.source (step : KahanAffineCoeffStep) : ℝ :=
  step.B * step.x + step.R * step.e

/-- Input contribution of one residual-aware affine coefficient step. -/
def KahanAffineCoeffStep.inputSource (step : KahanAffineCoeffStep) : ℝ :=
  step.B * step.x

/-- Retained-correction contribution of one residual-aware affine coefficient
step. -/
def KahanAffineCoeffStep.correctionSource
    (step : KahanAffineCoeffStep) : ℝ :=
  step.R * step.e

/-- The source contribution splits into the current-input part and the
retained-correction part. -/
theorem KahanAffineCoeffStep.source_eq_input_add_correction
    (step : KahanAffineCoeffStep) :
    step.source = step.inputSource + step.correctionSource := by
  rfl

/-- Product of the old-total coefficients along a coefficient-step suffix. -/
def kahanAffineCoeffTailProd : List KahanAffineCoeffStep → ℝ
  | [] => 1
  | step :: steps => step.A * kahanAffineCoeffTailProd steps

/-- Explicit unrolling of a residual-aware affine coefficient recurrence.

For each step, the source contribution is multiplied by the product of all
later old-total coefficients.  This is the product-form algebra needed before
the ordinary Kahan `mu_i` recursion can bound or absorb retained corrections. -/
def kahanAffineResidualUnroll : List KahanAffineCoeffStep → ℝ
  | [] => 0
  | step :: steps =>
      kahanAffineCoeffTailProd steps * step.source +
        kahanAffineResidualUnroll steps

/-- Product-form unrolling of only the current-input source contributions. -/
def kahanAffineInputUnroll : List KahanAffineCoeffStep → ℝ
  | [] => 0
  | step :: steps =>
      kahanAffineCoeffTailProd steps * step.inputSource +
        kahanAffineInputUnroll steps

/-- Product-form unrolling of only the retained-correction source
contributions. -/
def kahanAffineCorrectionUnroll : List KahanAffineCoeffStep → ℝ
  | [] => 0
  | step :: steps =>
      kahanAffineCoeffTailProd steps * step.correctionSource +
        kahanAffineCorrectionUnroll steps

/-- Absolute-value majorant for the retained-correction product-form
contribution. -/
def kahanAffineCorrectionAbsUnroll : List KahanAffineCoeffStep → ℝ
  | [] => 0
  | step :: steps =>
      |kahanAffineCoeffTailProd steps| * |step.correctionSource| +
        kahanAffineCorrectionAbsUnroll steps

/-- Indexed propagated budget for retained-correction source terms.

For a step list `step_0, ..., step_{k-1}`, this charges the `j`th correction
source by `R * E j` and the product bound `rho^(k-1-j)` for all later
old-total coefficients. -/
def kahanAffineCorrectionIndexedBudget
    (rho R : ℝ) (E : ℕ → ℝ) :
    List KahanAffineCoeffStep → ℝ
  | [] => 0
  | _step :: steps =>
      rho ^ steps.length * R * E 0 +
        kahanAffineCorrectionIndexedBudget rho R (fun j => E (j + 1)) steps

/-- Per-input coefficient induced by the current-input part of a residual-aware
affine Kahan coefficient unroll.

For the step at list index `i`, the coefficient is the current-input
coefficient `B_i` multiplied by all later old-total coefficients, minus `1`.
The propagated retained-correction contribution is kept separate and bounded
by `kahanAffineCorrectionIndexedBudget`. -/
noncomputable def kahanAffineInputCoeff
    (steps : List KahanAffineCoeffStep) (i : Fin steps.length) : ℝ :=
  kahanAffineCoeffTailProd (steps.drop (i.val + 1)) *
      (steps.get i).B - 1

/-- Folded residual-aware affine recurrence with an arbitrary initial total. -/
def kahanAffineResidualFold
    (steps : List KahanAffineCoeffStep) (init : ℝ) : ℝ :=
  steps.foldl
    (fun total step => step.A * total + step.source)
    init

/-- Product-form unrolling for the residual-aware affine recurrence.

This is a generic algebraic dependency for C4.5: once the Kahan prefix trace is
instantiated as a list of coefficient steps, the final compensated total splits
into the initial total multiplied by all old-total coefficients plus the sum of
all input and retained-correction source contributions propagated by later
coefficients. -/
theorem kahanAffineResidualFold_eq_tailProd_mul_init_add_unroll
    (steps : List KahanAffineCoeffStep) (init : ℝ) :
    kahanAffineResidualFold steps init =
      kahanAffineCoeffTailProd steps * init +
        kahanAffineResidualUnroll steps := by
  induction steps generalizing init with
  | nil =>
      simp [kahanAffineResidualFold, kahanAffineCoeffTailProd,
        kahanAffineResidualUnroll]
  | cons step steps ih =>
      dsimp [kahanAffineResidualFold]
      change kahanAffineResidualFold steps (step.A * init + step.source) =
        kahanAffineCoeffTailProd (step :: steps) * init +
          kahanAffineResidualUnroll (step :: steps)
      rw [ih (step.A * init + step.source)]
      dsimp [kahanAffineCoeffTailProd, kahanAffineResidualUnroll,
        KahanAffineCoeffStep.source]
      ring

/-- Product-form unrolling of the residual-aware affine recurrence from the
zero initial total. -/
theorem kahanAffineResidualFold_zero_eq_unroll
    (steps : List KahanAffineCoeffStep) :
    kahanAffineResidualFold steps 0 =
      kahanAffineResidualUnroll steps := by
  simpa using
    kahanAffineResidualFold_eq_tailProd_mul_init_add_unroll steps 0

/-- The residual-aware product-form unroll splits into current-input and
retained-correction propagated contributions. -/
theorem kahanAffineResidualUnroll_eq_input_add_correction
    (steps : List KahanAffineCoeffStep) :
    kahanAffineResidualUnroll steps =
      kahanAffineInputUnroll steps +
        kahanAffineCorrectionUnroll steps := by
  induction steps with
  | nil =>
      simp [kahanAffineResidualUnroll, kahanAffineInputUnroll,
        kahanAffineCorrectionUnroll]
  | cons step steps ih =>
      dsimp [kahanAffineResidualUnroll, kahanAffineInputUnroll,
        kahanAffineCorrectionUnroll, KahanAffineCoeffStep.source,
        KahanAffineCoeffStep.inputSource,
        KahanAffineCoeffStep.correctionSource]
      rw [ih]
      ring

/-- The residual-aware folded recurrence from zero splits into propagated
current-input and retained-correction contributions. -/
theorem kahanAffineResidualFold_zero_eq_input_add_correction
    (steps : List KahanAffineCoeffStep) :
    kahanAffineResidualFold steps 0 =
      kahanAffineInputUnroll steps +
        kahanAffineCorrectionUnroll steps := by
  rw [kahanAffineResidualFold_zero_eq_unroll]
  exact kahanAffineResidualUnroll_eq_input_add_correction steps

/-- Triangle-bound substrate for the propagated retained-correction
contribution. -/
theorem kahanAffineCorrectionUnroll_abs_le
    (steps : List KahanAffineCoeffStep) :
    |kahanAffineCorrectionUnroll steps| ≤
      kahanAffineCorrectionAbsUnroll steps := by
  induction steps with
  | nil =>
      simp [kahanAffineCorrectionUnroll, kahanAffineCorrectionAbsUnroll]
  | cons step steps ih =>
      dsimp [kahanAffineCorrectionUnroll,
        kahanAffineCorrectionAbsUnroll]
      calc
        |kahanAffineCoeffTailProd steps * step.correctionSource +
            kahanAffineCorrectionUnroll steps|
            ≤ |kahanAffineCoeffTailProd steps * step.correctionSource| +
                |kahanAffineCorrectionUnroll steps| := abs_add_le _ _
    _ = |kahanAffineCoeffTailProd steps| * |step.correctionSource| +
                |kahanAffineCorrectionUnroll steps| := by
              rw [abs_mul]
    _ ≤ |kahanAffineCoeffTailProd steps| * |step.correctionSource| +
                kahanAffineCorrectionAbsUnroll steps := by
              exact add_le_add (le_refl _) ih

/-- The propagated current-input part of a residual-aware affine unroll is a
source-term sum with per-input coefficients `kahanAffineInputCoeff`. -/
theorem kahanAffineInputUnroll_eq_sum_inputCoeff
    (steps : List KahanAffineCoeffStep) :
    kahanAffineInputUnroll steps =
      ∑ i : Fin steps.length,
        (steps.get i).x * (1 + kahanAffineInputCoeff steps i) := by
  induction steps with
  | nil =>
      simp [kahanAffineInputUnroll, kahanAffineInputCoeff]
  | cons step steps ih =>
      dsimp [kahanAffineInputUnroll, kahanAffineInputCoeff]
      change kahanAffineCoeffTailProd steps * step.inputSource +
          kahanAffineInputUnroll steps =
        ∑ i : Fin (steps.length + 1),
          ((step :: steps).get i).x *
            (1 + (kahanAffineCoeffTailProd (steps.drop i.val) *
              ((step :: steps).get i).B - 1))
      conv_rhs => rw [Fin.sum_univ_succ]
      rw [ih]
      simp [KahanAffineCoeffStep.inputSource, kahanAffineInputCoeff]
      ring

/-- Exact residual-aware affine fold from zero as a per-input coefficient sum
plus the propagated retained-correction contribution. -/
theorem kahanAffineResidualFold_zero_eq_sum_inputCoeff_add_correction
    (steps : List KahanAffineCoeffStep) :
    kahanAffineResidualFold steps 0 =
      (∑ i : Fin steps.length,
        (steps.get i).x * (1 + kahanAffineInputCoeff steps i)) +
        kahanAffineCorrectionUnroll steps := by
  rw [kahanAffineResidualFold_zero_eq_input_add_correction]
  rw [kahanAffineInputUnroll_eq_sum_inputCoeff]

/-- The additive residual left after replacing the current-input part by its
per-input coefficients is bounded by the retained-correction absolute unroll. -/
theorem kahanAffineResidualFold_zero_sub_sum_inputCoeff_abs_le
    (steps : List KahanAffineCoeffStep) :
    |kahanAffineResidualFold steps 0 -
      (∑ i : Fin steps.length,
        (steps.get i).x * (1 + kahanAffineInputCoeff steps i))| ≤
      kahanAffineCorrectionAbsUnroll steps := by
  have h :=
    kahanAffineResidualFold_zero_eq_sum_inputCoeff_add_correction steps
  rw [h]
  ring_nf
  exact kahanAffineCorrectionUnroll_abs_le steps

/-- If every old-total coefficient in a residual-aware affine step list has
absolute value at most `rho`, then the tail product is bounded by
`rho ^ steps.length`. -/
theorem kahanAffineCoeffTailProd_abs_le_pow
    {rho : ℝ} (hrho : 0 ≤ rho)
    (steps : List KahanAffineCoeffStep)
    (hA : ∀ step ∈ steps, |step.A| ≤ rho) :
    |kahanAffineCoeffTailProd steps| ≤ rho ^ steps.length := by
  induction steps with
  | nil =>
      simp [kahanAffineCoeffTailProd]
  | cons step steps ih =>
      dsimp [kahanAffineCoeffTailProd]
      rw [abs_mul]
      have hstep : |step.A| ≤ rho := hA step (by simp)
      have htail :
          |kahanAffineCoeffTailProd steps| ≤ rho ^ steps.length := by
        exact ih (fun step' hmem => hA step' (by simp [hmem]))
      have hmul :
          |step.A| * |kahanAffineCoeffTailProd steps| ≤
            rho * rho ^ steps.length := by
        exact mul_le_mul hstep htail (abs_nonneg _) hrho
      simpa [pow_succ, Nat.succ_eq_add_one, mul_comm, mul_left_comm,
        mul_assoc] using hmul

/-- If every old-total coefficient in a residual-aware affine step list is
within `eta` of one, then the full tail product is within
`(1 + eta)^m - 1` of one.

This is the product-collapse algebra needed to bound the product-form
`kahanAffineInputCoeff` coefficients. -/
theorem kahanAffineCoeffTailProd_abs_sub_one_le_pow_sub_one
    {eta : ℝ} (heta : 0 ≤ eta)
    (steps : List KahanAffineCoeffStep)
    (hA : ∀ step ∈ steps, |step.A - 1| ≤ eta) :
    |kahanAffineCoeffTailProd steps - 1| ≤
      (1 + eta) ^ steps.length - 1 := by
  induction steps with
  | nil =>
      simp [kahanAffineCoeffTailProd]
  | cons step steps ih =>
      dsimp [kahanAffineCoeffTailProd]
      have hstep : |step.A - 1| ≤ eta := hA step (by simp)
      have htail_close :
          |kahanAffineCoeffTailProd steps - 1| ≤
            (1 + eta) ^ steps.length - 1 := by
        exact ih (fun step' hmem => hA step' (by simp [hmem]))
      have hA_abs_all :
          ∀ step' ∈ steps, |step'.A| ≤ 1 + eta := by
        intro step' hmem
        have hclose := hA step' (by simp [hmem])
        calc
          |step'.A| = |(step'.A - 1) + 1| := by ring_nf
          _ ≤ |step'.A - 1| + |(1 : ℝ)| := abs_add_le _ _
          _ = |step'.A - 1| + 1 := by norm_num
          _ ≤ eta + 1 := by nlinarith [hclose]
          _ = 1 + eta := by ring
      have htail_abs :
          |kahanAffineCoeffTailProd steps| ≤
            (1 + eta) ^ steps.length := by
        exact kahanAffineCoeffTailProd_abs_le_pow
          (rho := 1 + eta) (by nlinarith) steps hA_abs_all
      have hprod :
          |(step.A - 1) * kahanAffineCoeffTailProd steps| ≤
            eta * (1 + eta) ^ steps.length := by
        rw [abs_mul]
        exact mul_le_mul hstep htail_abs (abs_nonneg _) heta
      calc
        |step.A * kahanAffineCoeffTailProd steps - 1|
            = |(step.A - 1) * kahanAffineCoeffTailProd steps +
                (kahanAffineCoeffTailProd steps - 1)| := by
              ring_nf
        _ ≤ |(step.A - 1) * kahanAffineCoeffTailProd steps| +
              |kahanAffineCoeffTailProd steps - 1| := abs_add_le _ _
        _ ≤ eta * (1 + eta) ^ steps.length +
              ((1 + eta) ^ steps.length - 1) := by
            nlinarith
        _ = (1 + eta) ^ (step :: steps).length - 1 := by
            simp [pow_succ]
            ring

/-- Generic product-radius bound for the product-form current-input coefficient.

If all later old-total coefficients are within `eta` of one and every current
input coefficient is within `beta` of one, then the per-input coefficient
`tailProd * B_i - 1` is bounded by the displayed product radius. -/
theorem kahanAffineInputCoeff_abs_le_productRadius
    {eta beta : ℝ} (heta : 0 ≤ eta)
    (steps : List KahanAffineCoeffStep)
    (hA : ∀ step ∈ steps, |step.A - 1| ≤ eta)
    (hB : ∀ step ∈ steps, |step.B - 1| ≤ beta)
    (i : Fin steps.length) :
    |kahanAffineInputCoeff steps i| ≤
      (1 + eta) ^ (steps.drop (i.val + 1)).length * beta +
        ((1 + eta) ^ (steps.drop (i.val + 1)).length - 1) := by
  let tailSteps := steps.drop (i.val + 1)
  let T := kahanAffineCoeffTailProd tailSteps
  let B := (steps.get i).B
  have htailA : ∀ step ∈ tailSteps, |step.A - 1| ≤ eta := by
    intro step hmem
    exact hA step (List.mem_of_mem_drop hmem)
  have htailAbs :
      |T| ≤ (1 + eta) ^ tailSteps.length := by
    have hA_abs : ∀ step ∈ tailSteps, |step.A| ≤ 1 + eta := by
      intro step hmem
      have hclose := htailA step hmem
      calc
        |step.A| = |(step.A - 1) + 1| := by ring_nf
        _ ≤ |step.A - 1| + |(1 : ℝ)| := abs_add_le _ _
        _ = |step.A - 1| + 1 := by norm_num
        _ ≤ eta + 1 := by nlinarith [hclose]
        _ = 1 + eta := by ring
    exact kahanAffineCoeffTailProd_abs_le_pow
      (rho := 1 + eta) (by nlinarith) tailSteps hA_abs
  have htailClose :
      |T - 1| ≤ (1 + eta) ^ tailSteps.length - 1 := by
    simpa [T] using
      kahanAffineCoeffTailProd_abs_sub_one_le_pow_sub_one
        heta tailSteps htailA
  have hBclose : |B - 1| ≤ beta := by
    exact hB (steps.get i) (List.get_mem steps i)
  have hprod :
      |T * (B - 1)| ≤
        (1 + eta) ^ tailSteps.length * beta := by
    rw [abs_mul]
    exact mul_le_mul htailAbs hBclose (abs_nonneg _)
      (pow_nonneg (by nlinarith : 0 ≤ 1 + eta) tailSteps.length)
  calc
    |kahanAffineInputCoeff steps i|
        = |T * B - 1| := by
            simp [kahanAffineInputCoeff, T, B, tailSteps]
    _ = |T * (B - 1) + (T - 1)| := by
            ring_nf
    _ ≤ |T * (B - 1)| + |T - 1| := abs_add_le _ _
    _ ≤ (1 + eta) ^ tailSteps.length * beta +
          ((1 + eta) ^ tailSteps.length - 1) := by
        nlinarith

/-- Generic indexed bound for the propagated retained-correction source
majorant.

This is the list-level algebra used by the ordinary Kahan coefficient route:
if later old-total products are bounded by `rho` per step and the `j`th
correction source is bounded by `R * E j`, then the absolute correction unroll
is bounded by the corresponding indexed propagated budget. -/
theorem kahanAffineCorrectionAbsUnroll_le_indexedBudget
    {rho R : ℝ} (hrho : 0 ≤ rho)
    (E : ℕ → ℝ) (hE : ∀ j, 0 ≤ E j)
    (steps : List KahanAffineCoeffStep)
    (hA : ∀ step ∈ steps, |step.A| ≤ rho)
    (hC :
      ∀ j (hj : j < steps.length),
        |(steps.get ⟨j, hj⟩).correctionSource| ≤ R * E j) :
    kahanAffineCorrectionAbsUnroll steps ≤
      kahanAffineCorrectionIndexedBudget rho R E steps := by
  induction steps generalizing E with
  | nil =>
      simp [kahanAffineCorrectionAbsUnroll,
        kahanAffineCorrectionIndexedBudget]
  | cons step steps ih =>
      dsimp [kahanAffineCorrectionAbsUnroll,
        kahanAffineCorrectionIndexedBudget]
      have htailA : ∀ step' ∈ steps, |step'.A| ≤ rho := by
        intro step' hmem
        exact hA step' (by simp [hmem])
      have htailC :
          ∀ j (hj : j < steps.length),
            |(steps.get ⟨j, hj⟩).correctionSource| ≤
              R * E (j + 1) := by
        intro j hj
        have hmain := hC (j + 1) (Nat.succ_lt_succ hj)
        simpa [List.get_cons_succ] using hmain
      have htail :=
        ih (fun j => E (j + 1)) (fun j => hE (j + 1))
          htailA htailC
      have htailProd :
          |kahanAffineCoeffTailProd steps| ≤ rho ^ steps.length :=
        kahanAffineCoeffTailProd_abs_le_pow hrho steps htailA
      have hheadC :
          |step.correctionSource| ≤ R * E 0 := by
        have hmain := hC 0 (Nat.succ_pos steps.length)
        simpa [List.get_cons_zero] using hmain
      have hhead :
          |kahanAffineCoeffTailProd steps| * |step.correctionSource| ≤
            rho ^ steps.length * (R * E 0) := by
        exact mul_le_mul htailProd hheadC (abs_nonneg _) (pow_nonneg hrho _)
      calc
        |kahanAffineCoeffTailProd steps| * |step.correctionSource| +
              kahanAffineCorrectionAbsUnroll steps
            ≤ rho ^ steps.length * (R * E 0) +
                kahanAffineCorrectionIndexedBudget rho R
                  (fun j => E (j + 1)) steps := by
              exact add_le_add hhead htail
        _ = rho ^ steps.length * R * E 0 +
              kahanAffineCorrectionIndexedBudget rho R
                (fun j => E (j + 1)) steps := by
              ring

/-- One-step coefficient form of the fully expanded Kahan compensated-total
recurrence.  This is the local algebraic form used before the per-input
Goldberg/Knuth coefficient recursion. -/
theorem kahanStepDeltaWitness_total_coefficients
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) :
    (kahanStepTrace fp x state).s + (kahanStepTrace fp x state).e =
      state.s * kahanTotalStateCoeff w.deltaS w.deltaSub w.deltaE +
        (x + state.e) *
          kahanTotalInputCoeff w.deltaY w.deltaS w.deltaSub w.deltaE := by
  rw [kahanStepDeltaWitness_total_fully_expanded fp x state w]
  dsimp [kahanTotalStateCoeff, kahanTotalInputCoeff]
  ring

/-- One-step compensated-total recurrence rewritten around the previous total
`state.s + state.e`.

The extra residual term is the retained-correction obstruction that the
ordinary Kahan backward-error recursion must still absorb or bound. -/
theorem kahanStepDeltaWitness_total_compensated_total_coefficients
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) :
    (kahanStepTrace fp x state).s + (kahanStepTrace fp x state).e =
      (state.s + state.e) *
          kahanTotalStateCoeff w.deltaS w.deltaSub w.deltaE +
        x * kahanTotalInputCoeff w.deltaY w.deltaS w.deltaSub w.deltaE +
        state.e *
          kahanTotalResidualCoeff w.deltaY w.deltaS w.deltaSub w.deltaE := by
  rw [kahanStepDeltaWitness_total_coefficients fp x state w]
  dsimp [kahanTotalResidualCoeff]
  ring

/-- The `temp` assignment in the finite-format Algorithm 4.2 wrapper. -/
theorem finiteKahanStepTrace_temp
    (fmt : FloatingPointFormat) (x : ℝ) (state : KahanState) :
    (finiteKahanStepTrace fmt x state).temp = state.s := by
  rfl

/-- The `y = x_i + e` assignment in the finite-format Algorithm 4.2 wrapper. -/
theorem finiteKahanStepTrace_y
    (fmt : FloatingPointFormat) (x : ℝ) (state : KahanState) :
    (finiteKahanStepTrace fmt x state).y =
      fmt.finiteRoundToEvenOp BasicOp.add x state.e := by
  rfl

/-- The `s = temp + y` assignment in the finite-format Algorithm 4.2 wrapper. -/
theorem finiteKahanStepTrace_s
    (fmt : FloatingPointFormat) (x : ℝ) (state : KahanState) :
    (finiteKahanStepTrace fmt x state).s =
      fmt.finiteRoundToEvenOp BasicOp.add
        (finiteKahanStepTrace fmt x state).temp
        (finiteKahanStepTrace fmt x state).y := by
  rfl

/-- The `e = (temp - s) + y` assignment in the finite-format Algorithm 4.2
wrapper, in the displayed evaluation order. -/
theorem finiteKahanStepTrace_e
    (fmt : FloatingPointFormat) (x : ℝ) (state : KahanState) :
    (finiteKahanStepTrace fmt x state).e =
      fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.finiteRoundToEvenOp BasicOp.sub
          (finiteKahanStepTrace fmt x state).temp
          (finiteKahanStepTrace fmt x state).s)
        (finiteKahanStepTrace fmt x state).y := by
  rfl

/-- Finite-format coherence for the first Algorithm 4.2 step: if the input is
finite representable, then the concrete finite round-to-even wrapper starts from
`s = 0; e = 0` exactly, returning `s = x` and zero correction.

This records the finite-format zero-add/subtract exactness that the abstract
`FPModel` interface intentionally does not assume. -/
theorem finiteKahanStepTrace_zero_of_finiteSystem
    (fmt : FloatingPointFormat) {x : ℝ} (hx : fmt.finiteSystem x) :
    finiteKahanStepTrace fmt x KahanState.zero =
      { temp := 0, y := x, s := x, e := 0 } := by
  have hy :
      fmt.finiteRoundToEvenOp BasicOp.add x 0 = x :=
    fmt.finiteRoundToEvenOp_add_zero_right_of_finiteSystem hx
  have hs :
      fmt.finiteRoundToEvenOp BasicOp.add 0 x = x :=
    fmt.finiteRoundToEvenOp_add_zero_of_finiteSystem hx
  have hsub :
      fmt.finiteRoundToEvenOp BasicOp.sub 0 x = -x := by
    have hfin : fmt.finiteSystem (BasicOp.exact BasicOp.sub 0 x) := by
      simpa [BasicOp.exact] using fmt.finiteSystem_neg hx
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub) (x := 0) (y := x) hfin)
  have he :
      fmt.finiteRoundToEvenOp BasicOp.add (-x) x = 0 := by
    have hfin : fmt.finiteSystem (BasicOp.exact BasicOp.add (-x) x) := by
      simpa [BasicOp.exact] using fmt.finiteSystem_zero
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.add) (x := -x) (y := x) hfin)
  simp [finiteKahanStepTrace, KahanState.zero, hy, hs, hsub, he]

/-- Persistent-state form of `finiteKahanStepTrace_zero_of_finiteSystem`. -/
theorem finiteKahanStep_zero_of_finiteSystem
    (fmt : FloatingPointFormat) {x : ℝ} (hx : fmt.finiteSystem x) :
    finiteKahanStep fmt x KahanState.zero = { s := x, e := 0 } := by
  have htrace := finiteKahanStepTrace_zero_of_finiteSystem fmt hx
  simpa [finiteKahanStep, KahanStepTrace.nextState] using congrArg KahanStepTrace.nextState htrace

/-- The local correction pair inside one Kahan step is exactly the Chapter 4
equation-(4.7) correction-formula trace applied to `temp` and `y`. -/
theorem kahanStepTrace_correctionFormulaTrace
    (fp : FPModel) (x : ℝ) (state : KahanState) :
    ({ s := (kahanStepTrace fp x state).s,
       e := (kahanStepTrace fp x state).e } : CorrectionFormulaTrace) =
      correctionFormulaTrace fp
        (kahanStepTrace fp x state).temp
        (kahanStepTrace fp x state).y := by
  simp [kahanStepTrace, correctionFormulaTrace]

/-- If the `y = x + e` add and the local correction formula are exact for one
Kahan step, then the compensated total `s + e` after the step equals the
previous compensated total plus the new input. -/
theorem kahanStepTrace_compensated_total_eq_of_exact_y_and_correction
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (hy : (kahanStepTrace fp x state).y = x + state.e)
    (hcorr :
      CorrectionFormulaTrace.exact state.s (kahanStepTrace fp x state).y
        ({ s := (kahanStepTrace fp x state).s,
           e := (kahanStepTrace fp x state).e } : CorrectionFormulaTrace)) :
    (kahanStepTrace fp x state).s + (kahanStepTrace fp x state).e =
      state.s + x + state.e := by
  have hcorr' := hcorr
  dsimp [CorrectionFormulaTrace.exact] at hcorr'
  rw [← hcorr', hy]
  ring

/-- Persistent-state version of
`kahanStepTrace_compensated_total_eq_of_exact_y_and_correction`. -/
theorem kahanStep_compensated_total_eq_of_exact_y_and_correction
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (hy : (kahanStepTrace fp x state).y = x + state.e)
    (hcorr :
      CorrectionFormulaTrace.exact state.s (kahanStepTrace fp x state).y
        ({ s := (kahanStepTrace fp x state).s,
           e := (kahanStepTrace fp x state).e } : CorrectionFormulaTrace)) :
    (kahanStep fp x state).s + (kahanStep fp x state).e =
      state.s + x + state.e := by
  simpa [kahanStep, KahanStepTrace.nextState] using
    kahanStepTrace_compensated_total_eq_of_exact_y_and_correction
      fp x state hy hcorr

/-- State after the first `k` Kahan steps over a length-`n` input. -/
noncomputable def kahanPrefixState (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : KahanState :=
  Fin.foldl k
    (fun state i =>
      kahanStep fp (v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) state)
    KahanState.zero

/-- One-element abstract Kahan prefix state under the explicit exact-zero-path
hypotheses from `kahanStep_zero_of_exact_zero_path`. -/
theorem kahanPrefixState_one_of_exact_zero_path
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (hn : 1 ≤ n)
    (haddRight :
      fp.fl_add (v ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩) 0 =
        v ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩)
    (hsub :
      fp.fl_sub 0 (v ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩) =
        -(v ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩))
    (hcancel :
      fp.fl_add (-(v ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩))
          (v ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩) =
        0) :
    kahanPrefixState fp v 1 hn =
      { s := v ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩, e := 0 } := by
  rw [kahanPrefixState, Fin.foldl_succ]
  simpa using
    kahanStep_zero_of_exact_zero_path
      fp haddRight hsub hcancel

/-- State after the first `k` finite-format Kahan steps over a length-`n`
input. -/
noncomputable def finiteKahanPrefixState (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : KahanState :=
  Fin.foldl k
    (fun state i =>
      finiteKahanStep fmt (v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) state)
    KahanState.zero

/-- One-element finite-format Kahan prefix state.  This is the prefix-level
version of the exact first-step coherence theorem and matches the source proof
initialization `S_1 = x_1`, with zero retained correction. -/
theorem finiteKahanPrefixState_one_of_finiteSystem
    (fmt : FloatingPointFormat) {n : ℕ} (v : Fin n → ℝ) (hn : 1 ≤ n)
    (hx :
      fmt.finiteSystem
        (v ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩)) :
    finiteKahanPrefixState fmt v 1 hn =
      { s := v ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩, e := 0 } := by
  rw [finiteKahanPrefixState, Fin.foldl_succ]
  simpa using
    finiteKahanStep_zero_of_finiteSystem fmt hx

/-- The per-index Kahan step trace, with the input state obtained by running
all earlier steps. -/
noncomputable def kahanTrace (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) : KahanStepTrace :=
  kahanStepTrace fp (v i)
    (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))

/-- Standard-model roundoff witnesses for the `i`th Algorithm 4.2 trace step,
with the input state supplied by the Kahan prefix trace. -/
noncomputable def kahanTrace_deltaWitness (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)) :=
  kahanStepTrace_deltaWitness fp (v i)
    (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))

/-- The `y` equation from the standard-model witness for the `i`th Kahan
trace step. -/
theorem kahanTrace_deltaWitness_y (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    (kahanTrace fp v i).y =
      (v i + (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)).e) *
        (1 + (kahanTrace_deltaWitness fp v i).deltaY) := by
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    (kahanTrace_deltaWitness fp v i).hy

/-- The `s` equation from the standard-model witness for the `i`th Kahan
trace step. -/
theorem kahanTrace_deltaWitness_s (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    (kahanTrace fp v i).s =
      ((kahanTrace fp v i).temp + (kahanTrace fp v i).y) *
        (1 + (kahanTrace_deltaWitness fp v i).deltaS) := by
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    (kahanTrace_deltaWitness fp v i).hs

/-- The `temp - s` subtraction equation from the standard-model witness for
the `i`th Kahan trace step. -/
theorem kahanTrace_deltaWitness_sub (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    fp.fl_sub (kahanTrace fp v i).temp (kahanTrace fp v i).s =
      ((kahanTrace fp v i).temp - (kahanTrace fp v i).s) *
        (1 + (kahanTrace_deltaWitness fp v i).deltaSub) := by
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    (kahanTrace_deltaWitness fp v i).hsub

/-- The correction `e` equation from the standard-model witness for the `i`th
Kahan trace step. -/
theorem kahanTrace_deltaWitness_e (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    (kahanTrace fp v i).e =
      (fp.fl_sub (kahanTrace fp v i).temp (kahanTrace fp v i).s +
        (kahanTrace fp v i).y) *
        (1 + (kahanTrace_deltaWitness fp v i).deltaE) := by
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    (kahanTrace_deltaWitness fp v i).he

/-- Expanded indexed recurrence for the updated Kahan sum at prefix trace step
`i`, with the `y = fl(x_i + e)` delta already substituted. -/
theorem kahanTrace_deltaWitness_s_expanded (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    (kahanTrace fp v i).s =
      ((kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)).s +
          (v i + (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)).e) *
            (1 + (kahanTrace_deltaWitness fp v i).deltaY)) *
        (1 + (kahanTrace_deltaWitness fp v i).deltaS) := by
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    kahanStepDeltaWitness_s_expanded fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))
      (kahanTrace_deltaWitness fp v i)

/-- Expanded indexed recurrence for the Kahan correction at prefix trace step
`i`, with the displayed subtraction delta already substituted. -/
theorem kahanTrace_deltaWitness_e_expanded (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    (kahanTrace fp v i).e =
      ((((kahanTrace fp v i).temp - (kahanTrace fp v i).s) *
          (1 + (kahanTrace_deltaWitness fp v i).deltaSub)) +
        (kahanTrace fp v i).y) *
        (1 + (kahanTrace_deltaWitness fp v i).deltaE) := by
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    kahanStepDeltaWitness_e_expanded fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))
      (kahanTrace_deltaWitness fp v i)

/-- Fully expanded indexed recurrence for the Kahan correction at prefix trace
step `i`, with no remaining trace-temporary terms on the right-hand side. -/
theorem kahanTrace_deltaWitness_e_fully_expanded (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    let y0 := (v i + state.e) *
      (1 + (kahanTrace_deltaWitness fp v i).deltaY)
    let s0 := (state.s + y0) *
      (1 + (kahanTrace_deltaWitness fp v i).deltaS)
    (kahanTrace fp v i).e =
      ((state.s - s0) *
          (1 + (kahanTrace_deltaWitness fp v i).deltaSub) +
        y0) *
        (1 + (kahanTrace_deltaWitness fp v i).deltaE) := by
  dsimp
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    kahanStepDeltaWitness_e_fully_expanded fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))
      (kahanTrace_deltaWitness fp v i)

/-- Fully expanded indexed recurrence for the compensated total at prefix trace
step `i`, the algebraic input for the Knuth/Goldberg coefficient recursion. -/
theorem kahanTrace_deltaWitness_total_fully_expanded (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    let y0 := (v i + state.e) *
      (1 + (kahanTrace_deltaWitness fp v i).deltaY)
    let s0 := (state.s + y0) *
      (1 + (kahanTrace_deltaWitness fp v i).deltaS)
    (kahanTrace fp v i).s + (kahanTrace fp v i).e =
      s0 +
        ((state.s - s0) *
            (1 + (kahanTrace_deltaWitness fp v i).deltaSub) +
          y0) *
          (1 + (kahanTrace_deltaWitness fp v i).deltaE) := by
  dsimp
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    kahanStepDeltaWitness_total_fully_expanded fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))
      (kahanTrace_deltaWitness fp v i)

/-- Indexed coefficient form of the Kahan compensated-total recurrence.  The
right-hand side has named coefficients for the previous running sum and the
current exact input-plus-correction term, ready for the ordinary Kahan
coefficient recursion. -/
theorem kahanTrace_deltaWitness_total_coefficients (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    (kahanTrace fp v i).s + (kahanTrace fp v i).e =
      state.s *
          kahanTotalStateCoeff
            (kahanTrace_deltaWitness fp v i).deltaS
            (kahanTrace_deltaWitness fp v i).deltaSub
            (kahanTrace_deltaWitness fp v i).deltaE +
        (v i + state.e) *
          kahanTotalInputCoeff
            (kahanTrace_deltaWitness fp v i).deltaY
            (kahanTrace_deltaWitness fp v i).deltaS
            (kahanTrace_deltaWitness fp v i).deltaSub
            (kahanTrace_deltaWitness fp v i).deltaE := by
  dsimp
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    kahanStepDeltaWitness_total_coefficients fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))
      (kahanTrace_deltaWitness fp v i)

/-- Indexed coefficient form of the Kahan retained-correction recurrence.
This is the `e`-component companion to the direct stored-sum recurrence below,
and supplies the coupled returned-sum/correction route. -/
theorem kahanTrace_deltaWitness_e_coefficients (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    (kahanTrace fp v i).e =
      state.s *
          kahanCorrectionStateCoeff
            (kahanTrace_deltaWitness fp v i).deltaS
            (kahanTrace_deltaWitness fp v i).deltaSub
            (kahanTrace_deltaWitness fp v i).deltaE +
        (v i + state.e) *
          kahanCorrectionInputCoeff
            (kahanTrace_deltaWitness fp v i).deltaY
            (kahanTrace_deltaWitness fp v i).deltaS
            (kahanTrace_deltaWitness fp v i).deltaSub
            (kahanTrace_deltaWitness fp v i).deltaE := by
  dsimp
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    kahanStepDeltaWitness_e_coefficients fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))
      (kahanTrace_deltaWitness fp v i)

/-- Indexed coefficient form of the directly expanded Kahan stored-sum
recurrence.  This exposes the returned-sum local coefficients without charging
the final retained correction as an independent residual. -/
theorem kahanTrace_deltaWitness_s_coefficients (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    (kahanTrace fp v i).s =
      state.s *
          kahanStoredSumStateCoeff
            (kahanTrace_deltaWitness fp v i).deltaS +
        (v i) *
          kahanStoredSumInputCoeff
            (kahanTrace_deltaWitness fp v i).deltaY
            (kahanTrace_deltaWitness fp v i).deltaS +
        state.e *
          kahanStoredSumInputCoeff
            (kahanTrace_deltaWitness fp v i).deltaY
            (kahanTrace_deltaWitness fp v i).deltaS := by
  dsimp
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    kahanStepDeltaWitness_s_coefficients fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))
      (kahanTrace_deltaWitness fp v i)

/-- Indexed local radius for the current-input coefficient in the direct
stored-sum recurrence. -/
theorem kahanTrace_deltaWitness_storedSumInputCoeff_abs_sub_one_le_two_u_plus_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |kahanStoredSumInputCoeff
        (kahanTrace_deltaWitness fp v i).deltaY
        (kahanTrace_deltaWitness fp v i).deltaS - 1| ≤
      2 * fp.u + fp.u ^ 2 :=
  kahanStoredSumInputCoeff_abs_sub_one_le_two_u_plus_u_sq fp.u_nonneg
    (kahanTrace_deltaWitness fp v i).h_deltaY
    (kahanTrace_deltaWitness fp v i).h_deltaS

/-- Indexed compensated-total recurrence rewritten around the previous
compensated total.  This is the exact prefix-trace input for the remaining
ordinary-Kahan `mu_i` recursion: besides the previous-total and current-input
coefficients, it exposes the retained-correction residual coefficient. -/
theorem kahanTrace_deltaWitness_total_compensated_total_coefficients
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    (kahanTrace fp v i).s + (kahanTrace fp v i).e =
      (state.s + state.e) *
          kahanTotalStateCoeff
            (kahanTrace_deltaWitness fp v i).deltaS
            (kahanTrace_deltaWitness fp v i).deltaSub
            (kahanTrace_deltaWitness fp v i).deltaE +
        (v i) *
          kahanTotalInputCoeff
            (kahanTrace_deltaWitness fp v i).deltaY
            (kahanTrace_deltaWitness fp v i).deltaS
            (kahanTrace_deltaWitness fp v i).deltaSub
            (kahanTrace_deltaWitness fp v i).deltaE +
        state.e *
          kahanTotalResidualCoeff
            (kahanTrace_deltaWitness fp v i).deltaY
            (kahanTrace_deltaWitness fp v i).deltaS
            (kahanTrace_deltaWitness fp v i).deltaSub
            (kahanTrace_deltaWitness fp v i).deltaE := by
  dsimp
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    kahanStepDeltaWitness_total_compensated_total_coefficients fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))
      (kahanTrace_deltaWitness fp v i)

/-- Indexed local absolute bound for the retained correction produced by one
Kahan prefix-trace step. -/
theorem kahanTrace_e_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    |(kahanTrace fp v i).e| ≤
      fp.u * (1 + fp.u) ^ 2 * |state.s| +
        fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
          |v i + state.e| := by
  dsimp
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    kahanStepDeltaWitness_e_abs_le fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))
      (kahanTrace_deltaWitness fp v i)

/-- Split-input indexed local absolute bound for the retained correction
produced by one Kahan prefix-trace step. -/
theorem kahanTrace_e_abs_le_split
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    |(kahanTrace fp v i).e| ≤
      fp.u * (1 + fp.u) ^ 2 * |state.s| +
        fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
          (|v i| + |state.e|) := by
  dsimp
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    kahanStepDeltaWitness_e_abs_le_split fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))
      (kahanTrace_deltaWitness fp v i)

/-- Local absolute bound for the stored sum produced by one Kahan step, in
terms of supplied majorants for the previous stored sum and correction. -/
theorem kahanStepDeltaWitness_s_abs_le_inputMajorants
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) {S E : ℝ}
    (hs : |state.s| ≤ S) (he : |state.e| ≤ E)
    (hS : 0 ≤ S) (hE : 0 ≤ E) :
    |(kahanStepTrace fp x state).s| ≤
      (1 + fp.u) * S + (1 + fp.u) ^ 2 * (|x| + E) := by
  have hdeltaY : |1 + w.deltaY| ≤ 1 + fp.u := by
    calc
      |1 + w.deltaY| ≤ |(1 : ℝ)| + |w.deltaY| :=
        abs_add_le 1 w.deltaY
      _ ≤ 1 + fp.u := by
        exact add_le_add (by norm_num) w.h_deltaY
  have hdeltaS : |1 + w.deltaS| ≤ 1 + fp.u := by
    calc
      |1 + w.deltaS| ≤ |(1 : ℝ)| + |w.deltaS| :=
        abs_add_le 1 w.deltaS
      _ ≤ 1 + fp.u := by
        exact add_le_add (by norm_num) w.h_deltaS
  have hcoef_nonneg : 0 ≤ 1 + fp.u := by
    nlinarith [fp.u_nonneg]
  have hxE_nonneg : 0 ≤ |x| + E := add_nonneg (abs_nonneg _) hE
  have hxe : |x + state.e| ≤ |x| + E :=
    (abs_add_le x state.e).trans (add_le_add (le_refl _) he)
  have hy :
      |(x + state.e) * (1 + w.deltaY)| ≤
        (|x| + E) * (1 + fp.u) := by
    calc
      |(x + state.e) * (1 + w.deltaY)|
          = |x + state.e| * |1 + w.deltaY| := abs_mul _ _
      _ ≤ (|x| + E) * (1 + fp.u) := by
        exact mul_le_mul hxe hdeltaY (abs_nonneg _) hxE_nonneg
  have hinside :
      |state.s + (x + state.e) * (1 + w.deltaY)| ≤
        S + (|x| + E) * (1 + fp.u) := by
    calc
      |state.s + (x + state.e) * (1 + w.deltaY)|
          ≤ |state.s| + |(x + state.e) * (1 + w.deltaY)| :=
        abs_add_le state.s ((x + state.e) * (1 + w.deltaY))
      _ ≤ S + (|x| + E) * (1 + fp.u) := add_le_add hs hy
  have hinside_nonneg :
      0 ≤ S + (|x| + E) * (1 + fp.u) :=
    add_nonneg hS (mul_nonneg hxE_nonneg hcoef_nonneg)
  calc
    |(kahanStepTrace fp x state).s|
        = |(state.s + (x + state.e) * (1 + w.deltaY)) *
            (1 + w.deltaS)| := by
          rw [kahanStepDeltaWitness_s_expanded fp x state w]
    _ = |state.s + (x + state.e) * (1 + w.deltaY)| *
          |1 + w.deltaS| := abs_mul _ _
    _ ≤ (S + (|x| + E) * (1 + fp.u)) * (1 + fp.u) := by
          exact mul_le_mul hinside hdeltaS (abs_nonneg _) hinside_nonneg
    _ = (1 + fp.u) * S + (1 + fp.u) ^ 2 * (|x| + E) := by
          ring

/-- Prefix-recursive majorant for the retained correction in Algorithm 4.2.

The recurrence follows the actual Kahan prefix order.  At each step it uses the
local retained-correction bound in terms of the previous stored sum, the current
input, and the previous correction majorant. -/
noncomputable def kahanCorrectionAbsMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    (k : ℕ) → k ≤ n → ℝ
  | 0, _hk => 0
  | k + 1, hk =>
      let hprev : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let idx : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let prev := kahanPrefixState fp v k hprev
      fp.u * (1 + fp.u) ^ 2 * |prev.s| +
        fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
          (|v idx| + kahanCorrectionAbsMajorant fp v k hprev)

/-- The retained-correction prefix majorant is nonnegative. -/
theorem kahanCorrectionAbsMajorant_nonneg
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      0 ≤ kahanCorrectionAbsMajorant fp v k hk
  | 0, _hk => by
      simp [kahanCorrectionAbsMajorant]
  | k + 1, hk => by
      let hprev : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let idx : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let prev := kahanPrefixState fp v k hprev
      have hih := kahanCorrectionAbsMajorant_nonneg fp v k hprev
      have hc1 : 0 ≤ fp.u * (1 + fp.u) ^ 2 := by
        exact mul_nonneg fp.u_nonneg (sq_nonneg (1 + fp.u))
      have hc2 : 0 ≤ fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) := by
        exact mul_nonneg hc1 (by nlinarith [fp.u_nonneg])
      dsimp [kahanCorrectionAbsMajorant]
      exact add_nonneg
        (mul_nonneg hc1 (abs_nonneg _))
        (mul_nonneg hc2 (add_nonneg (abs_nonneg _) hih))

/-- All-prefix retained-correction recurrence bound for Algorithm 4.2.

This is the prefix-level closure of the local `e` bound.  The majorant still
mentions actual stored sums; the coupled input-only majorant below supplies the
stored-sum-free replacement used by the remaining Goldberg/Knuth coefficient
recursion route. -/
theorem kahanPrefixState_e_abs_le_correctionMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      |(kahanPrefixState fp v k hk).e| ≤
        kahanCorrectionAbsMajorant fp v k hk
  | 0, _hk => by
      simp [kahanPrefixState, KahanState.zero,
        kahanCorrectionAbsMajorant]
  | k + 1, hk => by
      have hprev : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let idx : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let prev := kahanPrefixState fp v k hprev
      have hih := kahanPrefixState_e_abs_le_correctionMajorant fp v k hprev
      have hfoldPrefix :
          kahanPrefixState fp v (k + 1) hk =
            kahanStep fp (v idx) prev := by
        unfold kahanPrefixState
        rw [Fin.foldl_succ_last]
        rfl
      have hstep :
          |(kahanStep fp (v idx) prev).e| ≤
            fp.u * (1 + fp.u) ^ 2 * |prev.s| +
              fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
                (|v idx| + |prev.e|) := by
        simpa [kahanStep, KahanStepTrace.nextState] using
          kahanStepDeltaWitness_e_abs_le_split fp (v idx) prev
            (kahanStepTrace_deltaWitness fp (v idx) prev)
      have hcoef_nonneg :
          0 ≤ fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) := by
        exact mul_nonneg
          (mul_nonneg fp.u_nonneg (sq_nonneg (1 + fp.u)))
          (by nlinarith [fp.u_nonneg])
      have htail :
          fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
              (|v idx| + |prev.e|) ≤
            fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
              (|v idx| + kahanCorrectionAbsMajorant fp v k hprev) := by
        exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hih)
          hcoef_nonneg
      calc
        |(kahanPrefixState fp v (k + 1) hk).e|
            = |(kahanStep fp (v idx) prev).e| := by rw [hfoldPrefix]
        _ ≤ fp.u * (1 + fp.u) ^ 2 * |prev.s| +
              fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
                (|v idx| + |prev.e|) := hstep
        _ ≤ fp.u * (1 + fp.u) ^ 2 * |prev.s| +
              fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
                (|v idx| + kahanCorrectionAbsMajorant fp v k hprev) := by
            exact add_le_add (le_refl _) htail
        _ = kahanCorrectionAbsMajorant fp v (k + 1) hk := by
            rfl

/-- Coupled input-only majorants for the stored Kahan sum and retained
correction.

The `s` and `e` fields are no longer actual Kahan quantities.  They are
recursive nonnegative bounds depending only on previous majorants and source
input magnitudes.  The `e` recurrence is the previous correction majorant with
the actual stored-sum term replaced by the stored-sum majorant. -/
noncomputable def kahanInputAbsMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    (k : ℕ) → k ≤ n → KahanState
  | 0, _hk => { s := 0, e := 0 }
  | k + 1, hk =>
      let hprev : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let idx : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let prev := kahanInputAbsMajorant fp v k hprev
      { s := (1 + fp.u) * prev.s +
          (1 + fp.u) ^ 2 * (|v idx| + prev.e)
        e := fp.u * (1 + fp.u) ^ 2 * prev.s +
          fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
            (|v idx| + prev.e) }

/-- The coupled input-only Kahan majorants are nonnegative. -/
theorem kahanInputAbsMajorant_nonneg
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      0 ≤ (kahanInputAbsMajorant fp v k hk).s ∧
        0 ≤ (kahanInputAbsMajorant fp v k hk).e
  | 0, _hk => by
      simp [kahanInputAbsMajorant]
  | k + 1, hk => by
      let hprev : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let idx : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let prev := kahanInputAbsMajorant fp v k hprev
      have hih := kahanInputAbsMajorant_nonneg fp v k hprev
      have hu1_nonneg : 0 ≤ 1 + fp.u := by nlinarith [fp.u_nonneg]
      have hu1_sq_nonneg : 0 ≤ (1 + fp.u) ^ 2 := sq_nonneg (1 + fp.u)
      have hc1 : 0 ≤ fp.u * (1 + fp.u) ^ 2 := by
        exact mul_nonneg fp.u_nonneg hu1_sq_nonneg
      have hc2 : 0 ≤ fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) := by
        exact mul_nonneg hc1 (by nlinarith [fp.u_nonneg])
      have htail : 0 ≤ |v idx| + prev.e :=
        add_nonneg (abs_nonneg _) hih.2
      dsimp [kahanInputAbsMajorant]
      constructor
      · exact add_nonneg
          (mul_nonneg hu1_nonneg hih.1)
          (mul_nonneg hu1_sq_nonneg htail)
      · exact add_nonneg
          (mul_nonneg hc1 hih.1)
          (mul_nonneg hc2 htail)

/-- All-prefix input-only bounds for Algorithm 4.2's stored sum and retained
correction.

This closes the C4.5 dependency that removes actual stored-sum terms from the
retained-correction recurrence.  It is still a recursive majorant substrate,
not the final Goldberg/Knuth `mu_i` witness construction. -/
theorem kahanPrefixState_abs_le_inputMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      |(kahanPrefixState fp v k hk).s| ≤
          (kahanInputAbsMajorant fp v k hk).s ∧
        |(kahanPrefixState fp v k hk).e| ≤
          (kahanInputAbsMajorant fp v k hk).e
  | 0, _hk => by
      simp [kahanPrefixState, KahanState.zero, kahanInputAbsMajorant]
  | k + 1, hk => by
      have hprev : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let idx : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let prevState := kahanPrefixState fp v k hprev
      let prevMaj := kahanInputAbsMajorant fp v k hprev
      have hih := kahanPrefixState_abs_le_inputMajorant fp v k hprev
      have hmaj_nonneg := kahanInputAbsMajorant_nonneg fp v k hprev
      have hfoldPrefix :
          kahanPrefixState fp v (k + 1) hk =
            kahanStep fp (v idx) prevState := by
        unfold kahanPrefixState
        rw [Fin.foldl_succ_last]
        rfl
      have hs_step :
          |(kahanStep fp (v idx) prevState).s| ≤
            (1 + fp.u) * prevMaj.s +
              (1 + fp.u) ^ 2 * (|v idx| + prevMaj.e) := by
        simpa [kahanStep, KahanStepTrace.nextState, prevState, prevMaj] using
          kahanStepDeltaWitness_s_abs_le_inputMajorants
            fp (v idx) prevState
            (kahanStepTrace_deltaWitness fp (v idx) prevState)
            hih.1 hih.2 hmaj_nonneg.1 hmaj_nonneg.2
      have he_step :
          |(kahanStep fp (v idx) prevState).e| ≤
            fp.u * (1 + fp.u) ^ 2 * prevMaj.s +
              fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
                (|v idx| + prevMaj.e) := by
        have hlocal :
            |(kahanStep fp (v idx) prevState).e| ≤
              fp.u * (1 + fp.u) ^ 2 * |prevState.s| +
                fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
                  (|v idx| + |prevState.e|) := by
          simpa [kahanStep, KahanStepTrace.nextState] using
            kahanStepDeltaWitness_e_abs_le_split fp (v idx) prevState
              (kahanStepTrace_deltaWitness fp (v idx) prevState)
        have hc1 : 0 ≤ fp.u * (1 + fp.u) ^ 2 := by
          exact mul_nonneg fp.u_nonneg (sq_nonneg (1 + fp.u))
        have hc2 : 0 ≤ fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) := by
          exact mul_nonneg hc1 (by nlinarith [fp.u_nonneg])
        have hfirst :
            fp.u * (1 + fp.u) ^ 2 * |prevState.s| ≤
              fp.u * (1 + fp.u) ^ 2 * prevMaj.s :=
          mul_le_mul_of_nonneg_left hih.1 hc1
        have hsecond :
            fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
                (|v idx| + |prevState.e|) ≤
              fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
                (|v idx| + prevMaj.e) :=
          mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hih.2) hc2
        exact hlocal.trans (add_le_add hfirst hsecond)
      constructor
      · calc
          |(kahanPrefixState fp v (k + 1) hk).s|
              = |(kahanStep fp (v idx) prevState).s| := by rw [hfoldPrefix]
          _ ≤ (1 + fp.u) * prevMaj.s +
                (1 + fp.u) ^ 2 * (|v idx| + prevMaj.e) := hs_step
          _ = (kahanInputAbsMajorant fp v (k + 1) hk).s := by rfl
      · calc
          |(kahanPrefixState fp v (k + 1) hk).e|
              = |(kahanStep fp (v idx) prevState).e| := by rw [hfoldPrefix]
          _ ≤ fp.u * (1 + fp.u) ^ 2 * prevMaj.s +
                fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
                  (|v idx| + prevMaj.e) := he_step
          _ = (kahanInputAbsMajorant fp v (k + 1) hk).e := by rfl

/-- Stored-sum projection of
`kahanPrefixState_abs_le_inputMajorant`. -/
theorem kahanPrefixState_s_abs_le_inputMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    |(kahanPrefixState fp v k hk).s| ≤
      (kahanInputAbsMajorant fp v k hk).s :=
  (kahanPrefixState_abs_le_inputMajorant fp v k hk).1

/-- Retained-correction projection of
`kahanPrefixState_abs_le_inputMajorant`. -/
theorem kahanPrefixState_e_abs_le_inputMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    |(kahanPrefixState fp v k hk).e| ≤
      (kahanInputAbsMajorant fp v k hk).e :=
  (kahanPrefixState_abs_le_inputMajorant fp v k hk).2

private theorem list_foldl_ofFn_eq_fin_foldl {α β : Type*}
    (f : β → α → β) :
    ∀ (n : ℕ) (g : Fin n → α) (init : β),
      (List.ofFn g).foldl f init =
        Fin.foldl n (fun acc i => f acc (g i)) init
  | 0, _g, init => by
      simp [List.ofFn_zero]
  | n + 1, g, init => by
      rw [Fin.foldl_succ, List.ofFn_succ, List.foldl_cons]
      exact list_foldl_ofFn_eq_fin_foldl f n (fun i => g i.succ)
        (f init (g 0))

/-! ### Coupled returned-sum/correction coefficient recursion -/

/-- One coupled coefficient step for the direct Kahan `(s,e)` recurrence.

The step updates both the returned stored sum and the retained correction at
once, so later coefficient unrolls can preserve the cancellation between these
two fields instead of bounding the retained correction as an independent final
residual. -/
structure KahanCoupledCoeffStep where
  A : ℝ
  B : ℝ
  C : ℝ
  D : ℝ
  x : ℝ

/-- Apply one coupled coefficient step to a stored-sum/correction pair. -/
def KahanCoupledCoeffStep.next
    (step : KahanCoupledCoeffStep) (state : KahanState) : KahanState :=
  { s := state.s * step.A + step.x * step.B + state.e * step.B
    e := state.s * step.C + (step.x + state.e) * step.D }

/-- Homogeneous propagation part of one coupled coefficient step, with the
new source input suppressed. -/
def KahanCoupledCoeffStep.propagate
    (step : KahanCoupledCoeffStep) (state : KahanState) : KahanState :=
  { s := state.s * step.A + state.e * step.B
    e := state.s * step.C + state.e * step.D }

/-- Source vector injected by one coupled coefficient step. -/
def KahanCoupledCoeffStep.source (step : KahanCoupledCoeffStep) : KahanState :=
  { s := step.x * step.B, e := step.x * step.D }

/-- Unit source-coefficient vector injected by one coupled coefficient step,
before multiplication by the input value. -/
def KahanCoupledCoeffStep.sourceCoeff
    (step : KahanCoupledCoeffStep) : KahanState :=
  { s := step.B, e := step.D }

/-- Coefficient multiplying the previous stored sum when the coupled step is
viewed through the compensated total `s+e`. -/
def KahanCoupledCoeffStep.totalStateCoeff
    (step : KahanCoupledCoeffStep) : ℝ :=
  step.A + step.C

/-- Coefficient multiplying the current input and previous retained correction
when the coupled step is viewed through the compensated total `s+e`. -/
def KahanCoupledCoeffStep.totalInputCoeff
    (step : KahanCoupledCoeffStep) : ℝ :=
  step.B + step.D

/-- Residual coefficient left when the coupled total recurrence is rewritten
around the previous compensated total `state.s + state.e`. -/
def KahanCoupledCoeffStep.residualCoeff
    (step : KahanCoupledCoeffStep) : ℝ :=
  step.totalInputCoeff - step.totalStateCoeff

/-- Residual coefficient for the retained-correction row when the coupled step
is rewritten in `(compensated total, retained correction)` coordinates. -/
def KahanCoupledCoeffStep.correctionResidualCoeff
    (step : KahanCoupledCoeffStep) : ℝ :=
  step.D - step.C

/-- Old paired-total coefficient used when recovering the returned stored sum
after one homogeneous step.  Algebraically this is the direct stored-sum
old-state coefficient `A`. -/
def KahanCoupledCoeffStep.returnedStateCoeff
    (step : KahanCoupledCoeffStep) : ℝ :=
  step.totalStateCoeff - step.C

/-- Retained-correction coefficient used when recovering the returned stored
sum after one homogeneous step.  Algebraically this is `B - A`. -/
def KahanCoupledCoeffStep.returnedCorrectionCoeff
    (step : KahanCoupledCoeffStep) : ℝ :=
  step.residualCoeff - step.correctionResidualCoeff

/-- Homogeneous propagation in `(compensated total, retained correction)`
coordinates.  Here the input state's `s` field means the compensated total. -/
def KahanCoupledCoeffStep.propagateTotalCorrection
    (step : KahanCoupledCoeffStep) (state : KahanState) : KahanState :=
  { s := state.s * step.totalStateCoeff +
      state.e * step.residualCoeff
    e := state.s * step.C +
      state.e * step.correctionResidualCoeff }

/-- One coupled step is homogeneous propagation plus the current input source
vector. -/
theorem KahanCoupledCoeffStep.next_eq_propagate_add_source
    (step : KahanCoupledCoeffStep) (state : KahanState) :
    step.next state =
      KahanState.add (step.propagate state) step.source := by
  ext <;>
    dsimp [KahanCoupledCoeffStep.next, KahanCoupledCoeffStep.propagate,
      KahanCoupledCoeffStep.source, KahanState.add] <;>
    ring

/-- The source vector is the input value times the unit source-coefficient
vector. -/
theorem KahanCoupledCoeffStep.source_eq_smul_sourceCoeff
    (step : KahanCoupledCoeffStep) :
    step.source = KahanState.smul step.x step.sourceCoeff := by
  rfl

/-- Unit source coefficient in `(compensated total, retained correction)`
coordinates. -/
theorem KahanCoupledCoeffStep.sourceCoeff_totalCorrection
    (step : KahanCoupledCoeffStep) :
    KahanState.totalCorrection step.sourceCoeff =
      { s := step.totalInputCoeff, e := step.D } := by
  ext <;>
    simp [KahanState.totalCorrection,
      KahanCoupledCoeffStep.sourceCoeff,
      KahanCoupledCoeffStep.totalInputCoeff]

/-- Total component of a coupled source vector. -/
theorem KahanCoupledCoeffStep.source_total
    (step : KahanCoupledCoeffStep) :
    step.source.s + step.source.e =
      step.x * step.totalInputCoeff := by
  dsimp [KahanCoupledCoeffStep.source,
    KahanCoupledCoeffStep.totalInputCoeff]
  ring

/-- Total component after homogeneous coupled propagation. -/
theorem KahanCoupledCoeffStep.propagate_total
    (step : KahanCoupledCoeffStep) (state : KahanState) :
    (step.propagate state).s + (step.propagate state).e =
      state.s * step.totalStateCoeff +
        state.e * step.totalInputCoeff := by
  dsimp [KahanCoupledCoeffStep.propagate,
    KahanCoupledCoeffStep.totalStateCoeff,
    KahanCoupledCoeffStep.totalInputCoeff]
  ring

/-- Homogeneous propagation commutes with the change of coordinates from
`(s,e)` to `(s+e,e)`. -/
theorem KahanCoupledCoeffStep.propagate_totalCorrection
    (step : KahanCoupledCoeffStep) (state : KahanState) :
    KahanState.totalCorrection (step.propagate state) =
      step.propagateTotalCorrection
        (KahanState.totalCorrection state) := by
  ext <;>
    dsimp [KahanState.totalCorrection,
      KahanCoupledCoeffStep.propagate,
      KahanCoupledCoeffStep.propagateTotalCorrection,
      KahanCoupledCoeffStep.totalStateCoeff,
      KahanCoupledCoeffStep.totalInputCoeff,
      KahanCoupledCoeffStep.residualCoeff,
      KahanCoupledCoeffStep.correctionResidualCoeff] <;>
    ring

/-- The returned-coordinate old-state coefficient is exactly the direct
stored-sum coefficient `A`. -/
theorem KahanCoupledCoeffStep.returnedStateCoeff_eq_A
    (step : KahanCoupledCoeffStep) :
    step.returnedStateCoeff = step.A := by
  dsimp [KahanCoupledCoeffStep.returnedStateCoeff,
    KahanCoupledCoeffStep.totalStateCoeff]
  ring

/-- The returned-coordinate correction coefficient is exactly `B - A`. -/
theorem KahanCoupledCoeffStep.returnedCorrectionCoeff_eq_B_sub_A
    (step : KahanCoupledCoeffStep) :
    step.returnedCorrectionCoeff = step.B - step.A := by
  dsimp [KahanCoupledCoeffStep.returnedCorrectionCoeff,
    KahanCoupledCoeffStep.residualCoeff,
    KahanCoupledCoeffStep.correctionResidualCoeff,
    KahanCoupledCoeffStep.totalInputCoeff,
    KahanCoupledCoeffStep.totalStateCoeff]
  ring

/-- Returned stored-sum coordinate after paired-coordinate homogeneous
propagation.  This is the exact algebraic place where the ordinary returned
sum differs from the compensated-total route. -/
theorem KahanCoupledCoeffStep.propagateTotalCorrection_returned
    (step : KahanCoupledCoeffStep) (state : KahanState) :
    KahanState.returnedFromTotalCorrection
        (step.propagateTotalCorrection state) =
      state.s * step.returnedStateCoeff +
        state.e * step.returnedCorrectionCoeff := by
  dsimp [KahanState.returnedFromTotalCorrection,
    KahanCoupledCoeffStep.propagateTotalCorrection,
    KahanCoupledCoeffStep.returnedStateCoeff,
    KahanCoupledCoeffStep.returnedCorrectionCoeff,
    KahanCoupledCoeffStep.totalStateCoeff,
    KahanCoupledCoeffStep.residualCoeff,
    KahanCoupledCoeffStep.correctionResidualCoeff]
  ring

/-- One-step radius inequality for the returned stored-sum component in paired
coordinates.  Unlike the compensated-total recurrence, the old-state
coefficient here is the direct stored-sum coefficient and therefore carries a
first-order radius in the current abstract model. -/
theorem KahanCoupledCoeffStep.propagateTotalCorrection_returnedDev_abs_le_of_bounds
    (step : KahanCoupledCoeffStep) (state : KahanState)
    {eta theta : ℝ}
    (hState : |step.returnedStateCoeff - 1| ≤ eta)
    (hCorrection : |step.returnedCorrectionCoeff| ≤ theta) :
    |KahanState.returnedFromTotalCorrection
        (step.propagateTotalCorrection state) - 1| ≤
      |state.s - 1| * (1 + eta) + eta + |state.e| * theta := by
  rw [KahanCoupledCoeffStep.propagateTotalCorrection_returned]
  have hstateAbs : |step.returnedStateCoeff| ≤ 1 + eta := by
    calc
      |step.returnedStateCoeff| =
          |(step.returnedStateCoeff - 1) + 1| := by ring_nf
      _ ≤ |step.returnedStateCoeff - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ = |step.returnedStateCoeff - 1| + 1 := by norm_num
      _ ≤ eta + 1 := by nlinarith
      _ = 1 + eta := by ring
  have hrewrite :
      state.s * step.returnedStateCoeff +
          state.e * step.returnedCorrectionCoeff - 1 =
        (state.s - 1) * step.returnedStateCoeff +
          (step.returnedStateCoeff - 1) +
          state.e * step.returnedCorrectionCoeff := by
    ring
  rw [hrewrite]
  calc
    |(state.s - 1) * step.returnedStateCoeff +
        (step.returnedStateCoeff - 1) +
        state.e * step.returnedCorrectionCoeff|
        ≤ |(state.s - 1) * step.returnedStateCoeff +
            (step.returnedStateCoeff - 1)| +
            |state.e * step.returnedCorrectionCoeff| := abs_add_le _ _
    _ ≤ |(state.s - 1) * step.returnedStateCoeff| +
          |step.returnedStateCoeff - 1| +
          |state.e * step.returnedCorrectionCoeff| := by
        have h :=
          abs_add_le ((state.s - 1) * step.returnedStateCoeff)
            (step.returnedStateCoeff - 1)
        nlinarith
    _ = |state.s - 1| * |step.returnedStateCoeff| +
          |step.returnedStateCoeff - 1| +
          |state.e| * |step.returnedCorrectionCoeff| := by
        simp [abs_mul]
    _ ≤ |state.s - 1| * (1 + eta) + eta +
          |state.e| * theta := by
        have hfirst :
            |state.s - 1| * |step.returnedStateCoeff| ≤
              |state.s - 1| * (1 + eta) :=
          mul_le_mul_of_nonneg_left hstateAbs (abs_nonneg _)
        have hthird :
            |state.e| * |step.returnedCorrectionCoeff| ≤
              |state.e| * theta :=
          mul_le_mul_of_nonneg_left hCorrection (abs_nonneg _)
        nlinarith

/-- One-step radius inequality for the total component in paired
`(s+e,e)` coordinates.  This is the local induction inequality used by the
Goldberg-style coefficient route: the new total deviation is controlled by the
previous total deviation, the old-total coefficient deviation, and the retained
correction residual. -/
theorem KahanCoupledCoeffStep.propagateTotalCorrection_totalDev_abs_le
    (step : KahanCoupledCoeffStep) (state : KahanState) :
    |(step.propagateTotalCorrection state).s - 1| ≤
      |state.s - 1| * |step.totalStateCoeff| +
        |step.totalStateCoeff - 1| +
        |state.e| * |step.residualCoeff| := by
  dsimp [KahanCoupledCoeffStep.propagateTotalCorrection]
  let totalCoeff := step.totalStateCoeff
  let residual := step.residualCoeff
  have hrewrite :
      state.s * totalCoeff + state.e * residual - 1 =
        (state.s - 1) * totalCoeff + (totalCoeff - 1) +
          state.e * residual := by
    ring
  rw [hrewrite]
  calc
    |(state.s - 1) * totalCoeff + (totalCoeff - 1) +
        state.e * residual|
        ≤ |(state.s - 1) * totalCoeff + (totalCoeff - 1)| +
            |state.e * residual| := abs_add_le _ _
    _ ≤ |(state.s - 1) * totalCoeff| + |totalCoeff - 1| +
          |state.e * residual| := by
        have h :=
          abs_add_le ((state.s - 1) * totalCoeff) (totalCoeff - 1)
        nlinarith
    _ = |state.s - 1| * |step.totalStateCoeff| +
          |step.totalStateCoeff - 1| +
          |state.e| * |step.residualCoeff| := by
        simp [totalCoeff, residual, abs_mul]

/-- Bounded-coefficient form of
`KahanCoupledCoeffStep.propagateTotalCorrection_totalDev_abs_le`. -/
theorem KahanCoupledCoeffStep.propagateTotalCorrection_totalDev_abs_le_of_bounds
    (step : KahanCoupledCoeffStep) (state : KahanState)
    {eta rho : ℝ}
    (hTotal : |step.totalStateCoeff - 1| ≤ eta)
    (hResidual : |step.residualCoeff| ≤ rho) :
    |(step.propagateTotalCorrection state).s - 1| ≤
      |state.s - 1| * (1 + eta) + eta + |state.e| * rho := by
  have hbase :=
    KahanCoupledCoeffStep.propagateTotalCorrection_totalDev_abs_le
      step state
  have htotalAbs : |step.totalStateCoeff| ≤ 1 + eta := by
    calc
      |step.totalStateCoeff| =
          |(step.totalStateCoeff - 1) + 1| := by ring_nf
      _ ≤ |step.totalStateCoeff - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ = |step.totalStateCoeff - 1| + 1 := by norm_num
      _ ≤ eta + 1 := by nlinarith
      _ = 1 + eta := by ring
  have hfirst :
      |state.s - 1| * |step.totalStateCoeff| ≤
        |state.s - 1| * (1 + eta) :=
    mul_le_mul_of_nonneg_left htotalAbs (abs_nonneg _)
  have hthird :
      |state.e| * |step.residualCoeff| ≤ |state.e| * rho :=
    mul_le_mul_of_nonneg_left hResidual (abs_nonneg _)
  nlinarith

/-- One-step radius inequality for the retained-correction component in paired
`(s+e,e)` coordinates. -/
theorem KahanCoupledCoeffStep.propagateTotalCorrection_correction_abs_le
    (step : KahanCoupledCoeffStep) (state : KahanState) :
    |(step.propagateTotalCorrection state).e| ≤
      (|state.s - 1| + 1) * |step.C| +
        |state.e| * |step.correctionResidualCoeff| := by
  dsimp [KahanCoupledCoeffStep.propagateTotalCorrection]
  have hs_abs : |state.s| ≤ |state.s - 1| + 1 := by
    calc
      |state.s| = |(state.s - 1) + 1| := by ring_nf
      _ ≤ |state.s - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ = |state.s - 1| + 1 := by norm_num
  calc
    |state.s * step.C + state.e * step.correctionResidualCoeff|
        ≤ |state.s * step.C| +
            |state.e * step.correctionResidualCoeff| := abs_add_le _ _
    _ = |state.s| * |step.C| +
          |state.e| * |step.correctionResidualCoeff| := by
        simp [abs_mul]
    _ ≤ (|state.s - 1| + 1) * |step.C| +
          |state.e| * |step.correctionResidualCoeff| := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hs_abs (abs_nonneg _))
          (le_refl _)

/-- Bounded-coefficient form of
`KahanCoupledCoeffStep.propagateTotalCorrection_correction_abs_le`. -/
theorem KahanCoupledCoeffStep.propagateTotalCorrection_correction_abs_le_of_bounds
    (step : KahanCoupledCoeffStep) (state : KahanState)
    {sigma chi : ℝ}
    (hC : |step.C| ≤ sigma)
    (hCorrectionResidual : |step.correctionResidualCoeff| ≤ chi) :
    |(step.propagateTotalCorrection state).e| ≤
      (|state.s - 1| + 1) * sigma + |state.e| * chi := by
  have hbase :=
    KahanCoupledCoeffStep.propagateTotalCorrection_correction_abs_le
      step state
  have hfirst :
      (|state.s - 1| + 1) * |step.C| ≤
        (|state.s - 1| + 1) * sigma := by
    exact mul_le_mul_of_nonneg_left hC (by nlinarith [abs_nonneg (state.s - 1)])
  have hsecond :
      |state.e| * |step.correctionResidualCoeff| ≤ |state.e| * chi :=
    mul_le_mul_of_nonneg_left hCorrectionResidual (abs_nonneg _)
  nlinarith

/-- Total component after one coupled step, rewritten around the previous
compensated total plus the residual coefficient on the retained correction. -/
theorem KahanCoupledCoeffStep.next_total_eq_compensated_total
    (step : KahanCoupledCoeffStep) (state : KahanState) :
    (step.next state).s + (step.next state).e =
      step.totalStateCoeff * (state.s + state.e) +
        step.x * step.totalInputCoeff +
        state.e * step.residualCoeff := by
  dsimp [KahanCoupledCoeffStep.next,
    KahanCoupledCoeffStep.totalStateCoeff,
    KahanCoupledCoeffStep.totalInputCoeff,
    KahanCoupledCoeffStep.residualCoeff]
  ring

/-- Homogeneous coupled propagation is additive. -/
theorem KahanCoupledCoeffStep.propagate_add
    (step : KahanCoupledCoeffStep) (a b : KahanState) :
    step.propagate (KahanState.add a b) =
      KahanState.add (step.propagate a) (step.propagate b) := by
  ext <;>
    dsimp [KahanCoupledCoeffStep.propagate, KahanState.add] <;>
    ring

/-- Homogeneous coupled propagation commutes with scalar multiplication. -/
theorem KahanCoupledCoeffStep.propagate_smul
    (step : KahanCoupledCoeffStep) (c : ℝ) (state : KahanState) :
    step.propagate (KahanState.smul c state) =
      KahanState.smul c (step.propagate state) := by
  ext <;>
    dsimp [KahanCoupledCoeffStep.propagate, KahanState.smul] <;>
    ring

/-- Fold a list of coupled coefficient steps from an initial `(s,e)` state. -/
def kahanCoupledCoeffFold
    (steps : List KahanCoupledCoeffStep) (init : KahanState) : KahanState :=
  steps.foldl (fun state step => step.next state) init

/-- Homogeneous propagation through a list of coupled coefficient steps. -/
def kahanCoupledCoeffPropagate
    (steps : List KahanCoupledCoeffStep) (init : KahanState) : KahanState :=
  steps.foldl (fun state step => step.propagate state) init

/-- Homogeneous propagation through a list in
`(compensated total, retained correction)` coordinates. -/
def kahanCoupledTotalCorrectionPropagate
    (steps : List KahanCoupledCoeffStep) (init : KahanState) : KahanState :=
  steps.foldl (fun state step => step.propagateTotalCorrection state) init

/-- Goldberg's phantom final zero-input step in this file's sign convention.

Goldberg's proof of the compensated-summation coefficient bound appends a
formal zero input with exact local roundoff.  Since Higham's Algorithm 4.2 is
represented here with `y = x + e`, the exact zero step maps `(s,e)` to
`(s+e,0)`.  This theorem family is a source-route dependency for the remaining
equation (4.8) returned-sum coefficient collapse. -/
def kahanCoupledExactZeroStep : KahanCoupledCoeffStep :=
  { A := 1, B := 1, C := 0, D := 0, x := 0 }

/-- The phantom exact zero-input step maps `(s,e)` to `(s+e,0)`. -/
theorem kahanCoupledExactZeroStep_next (state : KahanState) :
    kahanCoupledExactZeroStep.next state =
      { s := state.s + state.e, e := 0 } := by
  ext <;>
    dsimp [kahanCoupledExactZeroStep, KahanCoupledCoeffStep.next] <;>
    ring

/-- The homogeneous part of the phantom exact zero-input step also maps
`(s,e)` to `(s+e,0)`. -/
theorem kahanCoupledExactZeroStep_propagate (state : KahanState) :
    kahanCoupledExactZeroStep.propagate state =
      { s := state.s + state.e, e := 0 } := by
  ext <;>
    dsimp [kahanCoupledExactZeroStep, KahanCoupledCoeffStep.propagate] <;>
    ring

/-- Appending Goldberg's exact zero-input step to a coupled fold turns the
final state into the compensated total with zero retained correction. -/
theorem kahanCoupledCoeffFold_append_exactZeroStep
    (steps : List KahanCoupledCoeffStep) (init : KahanState) :
    kahanCoupledCoeffFold (steps ++ [kahanCoupledExactZeroStep]) init =
      { s := (kahanCoupledCoeffFold steps init).s +
          (kahanCoupledCoeffFold steps init).e, e := 0 } := by
  unfold kahanCoupledCoeffFold
  rw [List.foldl_append]
  dsimp
  exact
    kahanCoupledExactZeroStep_next
      (steps.foldl (fun state step => step.next state) init)

/-- Appending Goldberg's exact zero-input step to homogeneous coefficient
propagation exposes the propagated compensated total in the returned-sum
component. -/
theorem kahanCoupledCoeffPropagate_append_exactZeroStep
    (steps : List KahanCoupledCoeffStep) (init : KahanState) :
    kahanCoupledCoeffPropagate (steps ++ [kahanCoupledExactZeroStep]) init =
      { s := (kahanCoupledCoeffPropagate steps init).s +
          (kahanCoupledCoeffPropagate steps init).e, e := 0 } := by
  unfold kahanCoupledCoeffPropagate
  rw [List.foldl_append]
  dsimp
  exact
    kahanCoupledExactZeroStep_propagate
      (steps.foldl (fun state step => step.propagate state) init)

/-- Product-form unroll of all source vectors in a coupled coefficient
recurrence.  The head source is propagated through all later steps; later
sources are accumulated recursively. -/
def kahanCoupledSourceUnroll : List KahanCoupledCoeffStep → KahanState
  | [] => KahanState.zero
  | step :: steps =>
      KahanState.add
        (kahanCoupledCoeffPropagate steps step.source)
        (kahanCoupledSourceUnroll steps)

/-- Homogeneous list propagation is additive. -/
theorem kahanCoupledCoeffPropagate_add
    (steps : List KahanCoupledCoeffStep) (a b : KahanState) :
    kahanCoupledCoeffPropagate steps (KahanState.add a b) =
      KahanState.add
        (kahanCoupledCoeffPropagate steps a)
        (kahanCoupledCoeffPropagate steps b) := by
  induction steps generalizing a b with
  | nil =>
      ext <;> dsimp [kahanCoupledCoeffPropagate, KahanState.add]
  | cons step steps ih =>
      dsimp [kahanCoupledCoeffPropagate]
      rw [KahanCoupledCoeffStep.propagate_add]
      exact ih (step.propagate a) (step.propagate b)

/-- Homogeneous list propagation commutes with scalar multiplication. -/
theorem kahanCoupledCoeffPropagate_smul
    (steps : List KahanCoupledCoeffStep) (c : ℝ) (state : KahanState) :
    kahanCoupledCoeffPropagate steps (KahanState.smul c state) =
      KahanState.smul c (kahanCoupledCoeffPropagate steps state) := by
  induction steps generalizing state with
  | nil =>
      ext <;> dsimp [kahanCoupledCoeffPropagate, KahanState.smul]
  | cons step steps ih =>
      dsimp [kahanCoupledCoeffPropagate]
      rw [KahanCoupledCoeffStep.propagate_smul]
      exact ih (step.propagate state)

/-- Homogeneous list propagation keeps the zero state zero. -/
theorem kahanCoupledCoeffPropagate_zero
    (steps : List KahanCoupledCoeffStep) :
    kahanCoupledCoeffPropagate steps KahanState.zero = KahanState.zero := by
  induction steps with
  | nil =>
      ext <;> dsimp [kahanCoupledCoeffPropagate, KahanState.zero]
  | cons step steps ih =>
      dsimp [kahanCoupledCoeffPropagate]
      have hstep :
          step.propagate KahanState.zero = KahanState.zero := by
        ext <;>
          dsimp [KahanCoupledCoeffStep.propagate, KahanState.zero] <;>
          ring
      rw [hstep]
      exact ih

/-- List propagation also commutes with the change from raw `(s,e)` to
`(s+e,e)` paired coordinates. -/
theorem kahanCoupledCoeffPropagate_totalCorrection_eq
    (steps : List KahanCoupledCoeffStep) (init : KahanState) :
    KahanState.totalCorrection
        (kahanCoupledCoeffPropagate steps init) =
      kahanCoupledTotalCorrectionPropagate steps
        (KahanState.totalCorrection init) := by
  induction steps generalizing init with
  | nil => rfl
  | cons step steps ih =>
      dsimp [kahanCoupledCoeffPropagate,
        kahanCoupledTotalCorrectionPropagate]
      have hih := ih (step.propagate init)
      dsimp [kahanCoupledCoeffPropagate,
        kahanCoupledTotalCorrectionPropagate] at hih
      rw [hih]
      rw [KahanCoupledCoeffStep.propagate_totalCorrection]

/-- Paired-coordinate coefficient majorant recurrence.

The `S` argument bounds the current total-coefficient deviation
`|totalCoeff - 1|`; the `E` argument bounds the retained-correction
coefficient.  Each list step applies the local paired inequalities with
constant bounds `eta`, `rho`, `sigma`, and `chi`. -/
def kahanCoupledPairedCoeffMajorant
    (eta rho sigma chi : ℝ) :
    List KahanCoupledCoeffStep → ℝ → ℝ → KahanState
  | [], S, E => { s := S, e := E }
  | _step :: steps, S, E =>
      kahanCoupledPairedCoeffMajorant eta rho sigma chi steps
        (S * (1 + eta) + eta + E * rho)
        ((S + 1) * sigma + E * chi)

/-- The paired-coordinate majorant has nonnegative components when started
from nonnegative radii and nonnegative update constants. -/
theorem kahanCoupledPairedCoeffMajorant_nonneg
    {eta rho sigma chi : ℝ}
    (heta : 0 ≤ eta) (hOneEta : 0 ≤ 1 + eta)
    (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma) (hchi : 0 ≤ chi) :
    ∀ (steps : List KahanCoupledCoeffStep) {S E : ℝ},
      0 ≤ S → 0 ≤ E →
      0 ≤ (kahanCoupledPairedCoeffMajorant eta rho sigma chi steps S E).s ∧
        0 ≤ (kahanCoupledPairedCoeffMajorant eta rho sigma chi steps S E).e
  | [], S, E, hS, hE => by
      simp [kahanCoupledPairedCoeffMajorant, hS, hE]
  | _step :: steps, S, E, hS, hE => by
      dsimp [kahanCoupledPairedCoeffMajorant]
      have hS' :
          0 ≤ S * (1 + eta) + eta + E * rho := by
        have hprodS : 0 ≤ S * (1 + eta) :=
          mul_nonneg hS hOneEta
        have hprodE : 0 ≤ E * rho := mul_nonneg hE hrho
        nlinarith
      have hE' :
          0 ≤ (S + 1) * sigma + E * chi := by
        have hS1 : 0 ≤ S + 1 := by nlinarith
        have hprodS : 0 ≤ (S + 1) * sigma :=
          mul_nonneg hS1 hsigma
        have hprodE : 0 ≤ E * chi := mul_nonneg hE hchi
        nlinarith
      exact
        kahanCoupledPairedCoeffMajorant_nonneg
          (eta := eta) (rho := rho) (sigma := sigma) (chi := chi)
          heta hOneEta hrho hsigma hchi steps hS' hE'

set_option maxHeartbeats 800000

/-- Conservative source-shaped collapse for the Kahan paired-coordinate
majorant.  If the initial total deviation is `2*u + A*u^2`, the initial
retained-correction coefficient is at most `12*u`, and the remaining suffix
has budget `(A + 200*m)*u <= 1`, then the propagated total deviation is at most
`2*u + (A + 200*m)*u^2` while the retained-correction coefficient stays
bounded by `12*u`.

The constants are deliberately loose: this is a dependency for the
Goldberg-style paired-coefficient route, not the final sharp hidden constant in
Higham's `O(n*u^2)`. -/
theorem kahanCoupledPairedCoeffMajorant_kahanConstants_le_two_u_plus
    {u A S E : ℝ}
    (hu0 : 0 ≤ u) (huSmall : u ≤ 1 / 64) (hA0 : 0 ≤ A) :
    ∀ (steps : List KahanCoupledCoeffStep),
      (A + 200 * (steps.length : ℝ)) * u ≤ 1 →
      S ≤ 2 * u + A * u ^ 2 →
      E ≤ 12 * u →
      let eta := 3 * u ^ 2
      let rho := 2 * u + 12 * u ^ 2
      let sigma := u * (1 + u) ^ 2
      let chi := u * (1 + u) ^ 2 * (3 + u)
      (kahanCoupledPairedCoeffMajorant eta rho sigma chi steps S E).s ≤
          2 * u + (A + 200 * (steps.length : ℝ)) * u ^ 2 ∧
        (kahanCoupledPairedCoeffMajorant eta rho sigma chi steps S E).e ≤
          12 * u
  | [], hBudget, hS, hE => by
      dsimp [kahanCoupledPairedCoeffMajorant]
      constructor
      · simpa using hS
      · exact hE
  | _step :: steps, hBudget, hS, hE => by
      dsimp [kahanCoupledPairedCoeffMajorant]
      have hu1 : u ≤ 1 := by nlinarith
      have hlen_nonneg : 0 ≤ (steps.length : ℝ) := by
        exact_mod_cast Nat.zero_le steps.length
      have hcons_len_nonneg :
          0 ≤ ((List.length (_step :: steps) : ℕ) : ℝ) := by
        exact_mod_cast Nat.zero_le (_step :: steps).length
      have hAu : A * u ≤ 1 := by
        have hle :
            A * u ≤ (A + 200 * (((_step :: steps).length : ℕ) : ℝ)) * u := by
          nlinarith [hu0, hcons_len_nonneg]
        exact hle.trans hBudget
      have hAu4 : A * u ^ 4 ≤ u ^ 3 := by
        have hu3_nonneg : 0 ≤ u ^ 3 := by nlinarith [hu0]
        have hmul := mul_le_mul_of_nonneg_right hAu hu3_nonneg
        nlinarith
      have hu3_le : u ^ 3 ≤ (1 / 64) * u ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right huSmall (sq_nonneg u)
        nlinarith
      have hOneEta : 0 ≤ 1 + 3 * u ^ 2 := by
        nlinarith [sq_nonneg u]
      have hrho_nonneg : 0 ≤ 2 * u + 12 * u ^ 2 := by
        nlinarith [hu0, sq_nonneg u]
      have hsigma_nonneg : 0 ≤ u * (1 + u) ^ 2 := by
        exact mul_nonneg hu0 (sq_nonneg (1 + u))
      have hchi_nonneg : 0 ≤ u * (1 + u) ^ 2 * (3 + u) := by
        exact mul_nonneg hsigma_nonneg (by nlinarith [hu0])
      have hsigma_le : u * (1 + u) ^ 2 ≤ 4 * u := by
        have h1u : 1 + u ≤ 2 := by nlinarith
        have h1u_nonneg : 0 ≤ 1 + u := by nlinarith
        have hsquare : (1 + u) ^ 2 ≤ 4 := by
          have hmul := mul_le_mul h1u h1u h1u_nonneg (by norm_num)
          nlinarith
        have hmul := mul_le_mul_of_nonneg_left hsquare hu0
        nlinarith
      have hchi_le : u * (1 + u) ^ 2 * (3 + u) ≤ 16 * u := by
        have h3u : 3 + u ≤ 4 := by nlinarith
        have h3u_nonneg : 0 ≤ 3 + u := by nlinarith [hu0]
        have h4u_nonneg : 0 ≤ 4 * u := by nlinarith [hu0]
        have hmul := mul_le_mul hsigma_le h3u h3u_nonneg h4u_nonneg
        nlinarith
      have hS_le_three_u : S ≤ 3 * u := by
        have hAu2 : A * u ^ 2 ≤ u := by
          have hmul := mul_le_mul_of_nonneg_right hAu hu0
          nlinarith
        nlinarith
      have hnextS :
          S * (1 + 3 * u ^ 2) + 3 * u ^ 2 +
              E * (2 * u + 12 * u ^ 2) ≤
            2 * u + (A + 200) * u ^ 2 := by
        have hS_mul :
            S * (1 + 3 * u ^ 2) ≤
              (2 * u + A * u ^ 2) * (1 + 3 * u ^ 2) := by
          exact mul_le_mul_of_nonneg_right hS hOneEta
        have hE_mul :
            E * (2 * u + 12 * u ^ 2) ≤
              (12 * u) * (2 * u + 12 * u ^ 2) := by
          exact mul_le_mul_of_nonneg_right hE hrho_nonneg
        nlinarith [hS_mul, hE_mul, hAu4, hu3_le]
      have hnextE :
          (S + 1) * (u * (1 + u) ^ 2) +
              E * (u * (1 + u) ^ 2 * (3 + u)) ≤
            12 * u := by
        have hS1 : S + 1 ≤ 1 + 3 * u := by nlinarith
        have hfirst :
            (S + 1) * (u * (1 + u) ^ 2) ≤
              (1 + 3 * u) * (4 * u) := by
          exact mul_le_mul hS1 hsigma_le hsigma_nonneg (by nlinarith)
        have hsecond :
            E * (u * (1 + u) ^ 2 * (3 + u)) ≤
              (12 * u) * (16 * u) := by
          exact mul_le_mul hE hchi_le hchi_nonneg (by nlinarith [hu0])
        have hu_sq_le : u ^ 2 ≤ (1 / 64) * u := by
          have hmul := mul_le_mul_of_nonneg_right huSmall hu0
          nlinarith
        nlinarith [hfirst, hsecond, hu_sq_le]
      have hBudgetTail :
          ((A + 200) + 200 * (steps.length : ℝ)) * u ≤ 1 := by
        have hEq :
            ((A + 200) + 200 * (steps.length : ℝ)) * u =
              (A + 200 * (((_step :: steps).length : ℕ) : ℝ)) * u := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring_nf
        rw [hEq]
        exact hBudget
      have htail :=
        kahanCoupledPairedCoeffMajorant_kahanConstants_le_two_u_plus
          (u := u) (A := A + 200)
          (S := S * (1 + 3 * u ^ 2) + 3 * u ^ 2 +
            E * (2 * u + 12 * u ^ 2))
          (E := (S + 1) * (u * (1 + u) ^ 2) +
            E * (u * (1 + u) ^ 2 * (3 + u)))
          hu0 huSmall (by nlinarith) steps hBudgetTail hnextS hnextE
      constructor
      · calc
          (kahanCoupledPairedCoeffMajorant (3 * u ^ 2)
              (2 * u + 12 * u ^ 2) (u * (1 + u) ^ 2)
              (u * (1 + u) ^ 2 * (3 + u)) steps
              (S * (1 + 3 * u ^ 2) + 3 * u ^ 2 +
                E * (2 * u + 12 * u ^ 2))
              ((S + 1) * (u * (1 + u) ^ 2) +
                E * (u * (1 + u) ^ 2 * (3 + u)))).s
              ≤ 2 * u + (A + 200 + 200 * (steps.length : ℝ)) * u ^ 2 :=
            htail.1
          _ = 2 * u + (A + 200 * (((steps.length + 1 : ℕ) : ℝ))) * u ^ 2 := by
            simp only [Nat.cast_add, Nat.cast_one]
            ring_nf
      · exact htail.2

/-- Paired-majorant collapse for the exact-correction-subtraction route.

When the correction-subtraction delta is zero, the local correction residual
is second order.  With the listed constants, both paired coordinates stay
within `u + O(m*u^2)` through a suffix of length `m`.  The constants are loose
on purpose; the theorem is a reusable majorant dependency for the ordinary
returned Kahan sum. -/
theorem kahanCoupledPairedCoeffMajorant_exactSubConstants_le_one_u_plus
    {u A S E : ℝ}
    (hu0 : 0 ≤ u) (huSmall : u ≤ 1 / 64) (hA0 : 0 ≤ A) :
    ∀ (steps : List KahanCoupledCoeffStep),
      (A + 40 * (steps.length : ℝ)) * u ≤ 1 →
      S ≤ u + A * u ^ 2 →
      E ≤ u + A * u ^ 2 →
      let eta := u ^ 2
      let rho := u + u ^ 2
      let sigma := u + u ^ 2
      let chi := 2 * u ^ 2
      (kahanCoupledPairedCoeffMajorant eta rho sigma chi steps S E).s ≤
          u + (A + 40 * (steps.length : ℝ)) * u ^ 2 ∧
        (kahanCoupledPairedCoeffMajorant eta rho sigma chi steps S E).e ≤
          u + (A + 40 * (steps.length : ℝ)) * u ^ 2
  | [], _hBudget, hS, hE => by
      dsimp [kahanCoupledPairedCoeffMajorant]
      constructor <;> simpa using ‹_›
  | _step :: steps, hBudget, hS, hE => by
      dsimp [kahanCoupledPairedCoeffMajorant]
      have hu1 : u ≤ 1 := by nlinarith
      have hcons_len_nonneg :
          0 ≤ ((List.length (_step :: steps) : ℕ) : ℝ) := by
        exact_mod_cast Nat.zero_le (_step :: steps).length
      have hAu : A * u ≤ 1 := by
        have hle :
            A * u ≤ (A + 40 * (((_step :: steps).length : ℕ) : ℝ)) * u := by
          nlinarith [hu0, hcons_len_nonneg]
        exact hle.trans hBudget
      have hu3_le_u2 : u ^ 3 ≤ u ^ 2 := by
        have h :=
          mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)
        nlinarith
      have hAu3 : A * u ^ 3 ≤ u ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hAu (sq_nonneg u)
        nlinarith
      have hAu4 : A * u ^ 4 ≤ u ^ 2 := by
        have hu3_nonneg : 0 ≤ u ^ 3 := by nlinarith [hu0]
        have hmul := mul_le_mul_of_nonneg_right hAu hu3_nonneg
        nlinarith [hmul, hu3_le_u2]
      have hOneEta : 0 ≤ 1 + u ^ 2 := by
        nlinarith [sq_nonneg u]
      have hrho_nonneg : 0 ≤ u + u ^ 2 := by
        nlinarith [hu0, sq_nonneg u]
      have hchi_nonneg : 0 ≤ 2 * u ^ 2 := by
        nlinarith [sq_nonneg u]
      have hnextS :
          S * (1 + u ^ 2) + u ^ 2 +
              E * (u + u ^ 2) ≤
            u + (A + 40) * u ^ 2 := by
        have hS_mul :
            S * (1 + u ^ 2) ≤
              (u + A * u ^ 2) * (1 + u ^ 2) := by
          exact mul_le_mul_of_nonneg_right hS hOneEta
        have hE_mul :
            E * (u + u ^ 2) ≤
              (u + A * u ^ 2) * (u + u ^ 2) := by
          exact mul_le_mul_of_nonneg_right hE hrho_nonneg
        nlinarith [hS_mul, hE_mul, hAu3, hAu4, hu3_le_u2]
      have hnextE :
          (S + 1) * (u + u ^ 2) + E * (2 * u ^ 2) ≤
            u + (A + 40) * u ^ 2 := by
        have hS1 : S + 1 ≤ 1 + u + A * u ^ 2 := by nlinarith
        have hfirst :
            (S + 1) * (u + u ^ 2) ≤
              (1 + u + A * u ^ 2) * (u + u ^ 2) := by
          exact mul_le_mul_of_nonneg_right hS1 hrho_nonneg
        have hsecond :
            E * (2 * u ^ 2) ≤
              (u + A * u ^ 2) * (2 * u ^ 2) := by
          exact mul_le_mul_of_nonneg_right hE hchi_nonneg
        nlinarith [hfirst, hsecond, hAu3, hAu4, hu3_le_u2, hA0]
      have hBudgetTail :
          ((A + 40) + 40 * (steps.length : ℝ)) * u ≤ 1 := by
        have hEq :
            ((A + 40) + 40 * (steps.length : ℝ)) * u =
              (A + 40 * (((_step :: steps).length : ℕ) : ℝ)) * u := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring_nf
        rw [hEq]
        exact hBudget
      have htail :=
        kahanCoupledPairedCoeffMajorant_exactSubConstants_le_one_u_plus
          (u := u) (A := A + 40)
          (S := S * (1 + u ^ 2) + u ^ 2 + E * (u + u ^ 2))
          (E := (S + 1) * (u + u ^ 2) + E * (2 * u ^ 2))
          hu0 huSmall (by nlinarith) steps hBudgetTail hnextS hnextE
      constructor
      · calc
          (kahanCoupledPairedCoeffMajorant (u ^ 2)
              (u + u ^ 2) (u + u ^ 2) (2 * u ^ 2) steps
              (S * (1 + u ^ 2) + u ^ 2 + E * (u + u ^ 2))
              ((S + 1) * (u + u ^ 2) + E * (2 * u ^ 2))).s
              ≤ u + (A + 40 + 40 * (steps.length : ℝ)) * u ^ 2 :=
            htail.1
          _ = u + (A + 40 * (((steps.length + 1 : ℕ) : ℝ))) * u ^ 2 := by
            simp only [Nat.cast_add, Nat.cast_one]
            ring_nf
      · calc
          (kahanCoupledPairedCoeffMajorant (u ^ 2)
              (u + u ^ 2) (u + u ^ 2) (2 * u ^ 2) steps
              (S * (1 + u ^ 2) + u ^ 2 + E * (u + u ^ 2))
              ((S + 1) * (u + u ^ 2) + E * (2 * u ^ 2))).e
              ≤ u + (A + 40 + 40 * (steps.length : ℝ)) * u ^ 2 :=
            htail.2
          _ = u + (A + 40 * (((steps.length + 1 : ℕ) : ℝ))) * u ^ 2 := by
            simp only [Nat.cast_add, Nat.cast_one]
            ring_nf

/-- Generic list-level paired-coordinate propagation bound.

If every step satisfies the local total-deviation and correction inequalities
with constants `eta`, `rho`, `sigma`, and `chi`, then propagation through the
whole list is bounded by `kahanCoupledPairedCoeffMajorant`. -/
theorem kahanCoupledTotalCorrectionPropagate_abs_le_pairedCoeffMajorant
    {eta rho sigma chi : ℝ}
    (heta : 0 ≤ eta) (hOneEta : 0 ≤ 1 + eta)
    (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma) (hchi : 0 ≤ chi)
    (steps : List KahanCoupledCoeffStep) (init : KahanState)
    {S E : ℝ}
    (hS0 : |init.s - 1| ≤ S) (hE0 : |init.e| ≤ E)
    (hS_nonneg : 0 ≤ S) (hE_nonneg : 0 ≤ E)
    (hTotal :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).s - 1| ≤
          |state.s - 1| * (1 + eta) + eta + |state.e| * rho)
    (hCorrection :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).e| ≤
          (|state.s - 1| + 1) * sigma + |state.e| * chi) :
    |(kahanCoupledTotalCorrectionPropagate steps init).s - 1| ≤
        (kahanCoupledPairedCoeffMajorant eta rho sigma chi steps S E).s ∧
      |(kahanCoupledTotalCorrectionPropagate steps init).e| ≤
        (kahanCoupledPairedCoeffMajorant eta rho sigma chi steps S E).e := by
  induction steps generalizing init S E with
  | nil =>
      simpa [kahanCoupledTotalCorrectionPropagate,
        kahanCoupledPairedCoeffMajorant] using And.intro hS0 hE0
  | cons step steps ih =>
      dsimp [kahanCoupledTotalCorrectionPropagate,
        kahanCoupledPairedCoeffMajorant]
      let next := step.propagateTotalCorrection init
      let S' := S * (1 + eta) + eta + E * rho
      let E' := (S + 1) * sigma + E * chi
      have hstepTotal :=
        hTotal step (by simp) init
      have hstepCorrection :=
        hCorrection step (by simp) init
      have hnextS : |next.s - 1| ≤ S' := by
        have hfirst :
            |init.s - 1| * (1 + eta) ≤ S * (1 + eta) :=
          mul_le_mul_of_nonneg_right hS0 hOneEta
        have hthird : |init.e| * rho ≤ E * rho :=
          mul_le_mul_of_nonneg_right hE0 hrho
        dsimp [next, S']
        nlinarith
      have hnextE : |next.e| ≤ E' := by
        have hfirst :
            (|init.s - 1| + 1) * sigma ≤ (S + 1) * sigma := by
          exact mul_le_mul_of_nonneg_right (by nlinarith) hsigma
        have hsecond : |init.e| * chi ≤ E * chi :=
          mul_le_mul_of_nonneg_right hE0 hchi
        dsimp [next, E']
        nlinarith
      have hS'_nonneg : 0 ≤ S' := by
        have hprodS : 0 ≤ S * (1 + eta) :=
          mul_nonneg hS_nonneg hOneEta
        have hprodE : 0 ≤ E * rho := mul_nonneg hE_nonneg hrho
        dsimp [S']
        nlinarith
      have hE'_nonneg : 0 ≤ E' := by
        have hS1 : 0 ≤ S + 1 := by nlinarith
        have hprodS : 0 ≤ (S + 1) * sigma :=
          mul_nonneg hS1 hsigma
        have hprodE : 0 ≤ E * chi := mul_nonneg hE_nonneg hchi
        dsimp [E']
        nlinarith
      have htailTotal :
          ∀ step' ∈ steps, ∀ state : KahanState,
            |(step'.propagateTotalCorrection state).s - 1| ≤
              |state.s - 1| * (1 + eta) + eta + |state.e| * rho := by
        intro step' hmem state
        exact hTotal step' (by simp [hmem]) state
      have htailCorrection :
          ∀ step' ∈ steps, ∀ state : KahanState,
            |(step'.propagateTotalCorrection state).e| ≤
              (|state.s - 1| + 1) * sigma + |state.e| * chi := by
        intro step' hmem state
        exact hCorrection step' (by simp [hmem]) state
      exact ih next hnextS hnextE hS'_nonneg hE'_nonneg
        htailTotal htailCorrection

/-- Generic coupled affine unroll: folding coupled steps equals the
homogeneous propagation of the initial state plus all propagated source
vectors. -/
theorem kahanCoupledCoeffFold_eq_propagate_add_sourceUnroll
    (steps : List KahanCoupledCoeffStep) (init : KahanState) :
    kahanCoupledCoeffFold steps init =
      KahanState.add
        (kahanCoupledCoeffPropagate steps init)
        (kahanCoupledSourceUnroll steps) := by
  induction steps generalizing init with
  | nil =>
      ext <;>
        dsimp [kahanCoupledCoeffFold, kahanCoupledCoeffPropagate,
          kahanCoupledSourceUnroll, KahanState.add, KahanState.zero] <;>
        ring
  | cons step steps ih =>
      dsimp [kahanCoupledCoeffFold, kahanCoupledCoeffPropagate,
        kahanCoupledSourceUnroll]
      have hih := ih (step.next init)
      dsimp [kahanCoupledCoeffFold] at hih
      rw [hih]
      rw [KahanCoupledCoeffStep.next_eq_propagate_add_source]
      rw [kahanCoupledCoeffPropagate_add]
      ext <;> dsimp [KahanState.add, kahanCoupledCoeffPropagate] <;>
        ring_nf

/-- Zero-initial coupled folds are exactly the propagated-source unroll. -/
theorem kahanCoupledCoeffFold_zero_eq_sourceUnroll
    (steps : List KahanCoupledCoeffStep) :
    kahanCoupledCoeffFold steps KahanState.zero =
      kahanCoupledSourceUnroll steps := by
  rw [kahanCoupledCoeffFold_eq_propagate_add_sourceUnroll]
  rw [kahanCoupledCoeffPropagate_zero]
  ext <;> dsimp [KahanState.add, KahanState.zero] <;> ring

/-- Source-vector unroll form of Goldberg's phantom exact zero-input step. -/
theorem kahanCoupledSourceUnroll_append_exactZeroStep
    (steps : List KahanCoupledCoeffStep) :
    kahanCoupledSourceUnroll (steps ++ [kahanCoupledExactZeroStep]) =
      { s := (kahanCoupledSourceUnroll steps).s +
          (kahanCoupledSourceUnroll steps).e, e := 0 } := by
  rw [← kahanCoupledCoeffFold_zero_eq_sourceUnroll
    (steps ++ [kahanCoupledExactZeroStep])]
  rw [kahanCoupledCoeffFold_append_exactZeroStep]
  rw [kahanCoupledCoeffFold_zero_eq_sourceUnroll]

/-- Per-input coupled source coefficient vector induced by the source-vector
unroll.  For the step at list index `i`, this is the unit source vector
propagated through all later coupled steps. -/
noncomputable def kahanCoupledSourceCoeff
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) :
    KahanState :=
  kahanCoupledCoeffPropagate
    (steps.drop (i.val + 1)) (steps.get i).sourceCoeff

/-- Per-input coupled source coefficient in
`(compensated total, retained correction)` coordinates. -/
noncomputable def kahanCoupledSourceTotalCorrectionCoeff
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) :
    KahanState :=
  KahanState.totalCorrection (kahanCoupledSourceCoeff steps i)

/-- The propagated source coefficient in paired coordinates is exactly the
source coefficient transformed to `(s+e,e)` and propagated by the transformed
list recurrence. -/
theorem kahanCoupledSourceCoeff_totalCorrection_eq
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) :
    kahanCoupledSourceTotalCorrectionCoeff steps i =
      kahanCoupledTotalCorrectionPropagate
        (steps.drop (i.val + 1))
        (KahanState.totalCorrection (steps.get i).sourceCoeff) := by
  dsimp [kahanCoupledSourceTotalCorrectionCoeff, kahanCoupledSourceCoeff]
  exact kahanCoupledCoeffPropagate_totalCorrection_eq
    (steps.drop (i.val + 1)) (steps.get i).sourceCoeff

/-- Generic paired-majorant bound for a propagated source coefficient.  This
packages the list-level paired-coordinate induction at the exact place where a
source coefficient is propagated through all later coupled steps. -/
theorem kahanCoupledSourceTotalCorrectionCoeff_abs_le_pairedCoeffMajorant
    {eta rho sigma chi : ℝ}
    (heta : 0 ≤ eta) (hOneEta : 0 ≤ 1 + eta)
    (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma) (hchi : 0 ≤ chi)
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length)
    {S E : ℝ}
    (hS0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).s - 1| ≤ S)
    (hE0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).e| ≤ E)
    (hS_nonneg : 0 ≤ S) (hE_nonneg : 0 ≤ E)
    (hTotal :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).s - 1| ≤
          |state.s - 1| * (1 + eta) + eta + |state.e| * rho)
    (hCorrection :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).e| ≤
          (|state.s - 1| + 1) * sigma + |state.e| * chi) :
    |(kahanCoupledSourceTotalCorrectionCoeff steps i).s - 1| ≤
        (kahanCoupledPairedCoeffMajorant eta rho sigma chi
          (steps.drop (i.val + 1)) S E).s ∧
      |(kahanCoupledSourceTotalCorrectionCoeff steps i).e| ≤
        (kahanCoupledPairedCoeffMajorant eta rho sigma chi
          (steps.drop (i.val + 1)) S E).e := by
  have htailTotal :
      ∀ step ∈ steps.drop (i.val + 1), ∀ state : KahanState,
        |(step.propagateTotalCorrection state).s - 1| ≤
          |state.s - 1| * (1 + eta) + eta + |state.e| * rho := by
    intro step hmem state
    exact hTotal step (List.mem_of_mem_drop hmem) state
  have htailCorrection :
      ∀ step ∈ steps.drop (i.val + 1), ∀ state : KahanState,
        |(step.propagateTotalCorrection state).e| ≤
          (|state.s - 1| + 1) * sigma + |state.e| * chi := by
    intro step hmem state
    exact hCorrection step (List.mem_of_mem_drop hmem) state
  have hprop :=
    kahanCoupledTotalCorrectionPropagate_abs_le_pairedCoeffMajorant
      (eta := eta) (rho := rho) (sigma := sigma) (chi := chi)
      heta hOneEta hrho hsigma hchi
      (steps.drop (i.val + 1))
      (KahanState.totalCorrection (steps.get i).sourceCoeff)
      hS0 hE0 hS_nonneg hE_nonneg htailTotal htailCorrection
  simpa [kahanCoupledSourceCoeff_totalCorrection_eq steps i] using hprop

/-- Generic triangle-route bound for a returned source coefficient.

This is the formal version of the weak route that bounds the ordinary returned
coefficient by the paired total deviation plus the retained-correction
coefficient.  It is useful as an audit theorem, but by itself it preserves a
first-order correction term and therefore does not close Higham equation (4.8)'s
`2*u + O(n*u^2)` coefficient. -/
theorem kahanCoupledSourceCoeff_s_abs_sub_one_le_pairedCoeffMajorant_sum
    {eta rho sigma chi : ℝ}
    (heta : 0 ≤ eta) (hOneEta : 0 ≤ 1 + eta)
    (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma) (hchi : 0 ≤ chi)
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length)
    {S E : ℝ}
    (hS0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).s - 1| ≤ S)
    (hE0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).e| ≤ E)
    (hS_nonneg : 0 ≤ S) (hE_nonneg : 0 ≤ E)
    (hTotal :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).s - 1| ≤
          |state.s - 1| * (1 + eta) + eta + |state.e| * rho)
    (hCorrection :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).e| ≤
          (|state.s - 1| + 1) * sigma + |state.e| * chi) :
    |(kahanCoupledSourceCoeff steps i).s - 1| ≤
      (kahanCoupledPairedCoeffMajorant eta rho sigma chi
        (steps.drop (i.val + 1)) S E).s +
      (kahanCoupledPairedCoeffMajorant eta rho sigma chi
        (steps.drop (i.val + 1)) S E).e := by
  have hpair :=
    kahanCoupledSourceTotalCorrectionCoeff_abs_le_pairedCoeffMajorant
      (eta := eta) (rho := rho) (sigma := sigma) (chi := chi)
      heta hOneEta hrho hsigma hchi steps i
      hS0 hE0 hS_nonneg hE_nonneg hTotal hCorrection
  let a := kahanCoupledSourceCoeff steps i
  have htri :
      |a.s - 1| ≤
        |(KahanState.totalCorrection a).s - 1| +
          |(KahanState.totalCorrection a).e| := by
    have hrewrite :
        a.s - 1 = (a.s + a.e - 1) - a.e := by ring
    rw [hrewrite]
    simpa [KahanState.totalCorrection, sub_eq_add_neg, abs_neg] using
      abs_add_le (a.s + a.e - 1) (-a.e)
  exact htri.trans (add_le_add hpair.1 hpair.2)

/-- Generic returned-coefficient collapse for the exact-subtraction local
constants.

If the source coefficient starts with both paired coordinates bounded by
`u + A*u^2`, and every later step satisfies the exact-subtraction paired
inequalities, then the ordinary returned source coefficient has the
source-shaped radius `2*u + O(m*u^2)`. -/
theorem kahanCoupledSourceCoeff_s_abs_sub_one_le_exactSubMajorant
    {u A S E : ℝ}
    (hu0 : 0 ≤ u) (huSmall : u ≤ 1 / 64) (hA0 : 0 ≤ A)
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length)
    (hBudget :
      (A + 40 * ((steps.drop (i.val + 1)).length : ℝ)) * u ≤ 1)
    (hS0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).s - 1| ≤ S)
    (hE0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).e| ≤ E)
    (hS_nonneg : 0 ≤ S) (hE_nonneg : 0 ≤ E)
    (hS_le : S ≤ u + A * u ^ 2)
    (hE_le : E ≤ u + A * u ^ 2)
    (hTotal :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).s - 1| ≤
          |state.s - 1| * (1 + u ^ 2) + u ^ 2 +
            |state.e| * (u + u ^ 2))
    (hCorrection :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).e| ≤
          (|state.s - 1| + 1) * (u + u ^ 2) +
            |state.e| * (2 * u ^ 2)) :
    |(kahanCoupledSourceCoeff steps i).s - 1| ≤
      2 * u +
        2 * (A + 40 * ((steps.drop (i.val + 1)).length : ℝ)) *
          u ^ 2 := by
  let suffix := steps.drop (i.val + 1)
  have hOneEta : 0 ≤ 1 + u ^ 2 := by
    nlinarith [sq_nonneg u]
  have hrho : 0 ≤ u + u ^ 2 := by
    nlinarith [hu0, sq_nonneg u]
  have hchi : 0 ≤ 2 * u ^ 2 := by
    nlinarith [sq_nonneg u]
  have hmajorant :=
    kahanCoupledSourceCoeff_s_abs_sub_one_le_pairedCoeffMajorant_sum
      (eta := u ^ 2) (rho := u + u ^ 2)
      (sigma := u + u ^ 2) (chi := 2 * u ^ 2)
      (by nlinarith [sq_nonneg u]) hOneEta hrho hrho hchi
      steps i hS0 hE0 hS_nonneg hE_nonneg hTotal hCorrection
  have hcollapse :=
    kahanCoupledPairedCoeffMajorant_exactSubConstants_le_one_u_plus
      (u := u) (A := A) (S := S) (E := E)
      hu0 huSmall hA0 suffix
      (by simpa [suffix] using hBudget) hS_le hE_le
  calc
    |(kahanCoupledSourceCoeff steps i).s - 1|
        ≤ (kahanCoupledPairedCoeffMajorant (u ^ 2) (u + u ^ 2)
            (u + u ^ 2) (2 * u ^ 2) suffix S E).s +
          (kahanCoupledPairedCoeffMajorant (u ^ 2) (u + u ^ 2)
            (u + u ^ 2) (2 * u ^ 2) suffix S E).e := by
          simpa [suffix] using hmajorant
    _ ≤ (u + (A + 40 * (suffix.length : ℝ)) * u ^ 2) +
          (u + (A + 40 * (suffix.length : ℝ)) * u ^ 2) := by
          exact add_le_add hcollapse.1 hcollapse.2
    _ = 2 * u + 2 * (A + 40 * (suffix.length : ℝ)) * u ^ 2 := by
          ring
    _ = 2 * u +
        2 * (A + 40 * ((steps.drop (i.val + 1)).length : ℝ)) *
          u ^ 2 := by
          simp [suffix]

/-- Returned-stored-sum component of the coupled source-vector unroll as an
explicit per-input coefficient sum. -/
theorem kahanCoupledSourceUnroll_s_eq_sum_sourceCoeff
    (steps : List KahanCoupledCoeffStep) :
    (kahanCoupledSourceUnroll steps).s =
      ∑ i : Fin steps.length,
        (steps.get i).x * (kahanCoupledSourceCoeff steps i).s := by
  induction steps with
  | nil => rfl
  | cons step steps ih =>
      dsimp [kahanCoupledSourceUnroll, KahanState.add]
      change
        (kahanCoupledCoeffPropagate steps step.source).s +
            (kahanCoupledSourceUnroll steps).s =
          ∑ i : Fin (steps.length + 1),
            ((step :: steps).get i).x *
              (kahanCoupledSourceCoeff (step :: steps) i).s
      conv_rhs => rw [Fin.sum_univ_succ]
      rw [ih]
      have hprop :
          kahanCoupledCoeffPropagate steps step.source =
            KahanState.smul step.x
              (kahanCoupledCoeffPropagate steps step.sourceCoeff) := by
        rw [KahanCoupledCoeffStep.source_eq_smul_sourceCoeff]
        exact kahanCoupledCoeffPropagate_smul
          steps step.x step.sourceCoeff
      rw [hprop]
      simp [kahanCoupledSourceCoeff, KahanState.smul]

/-- Retained-correction component of the coupled source-vector unroll as an
explicit per-input coefficient sum. -/
theorem kahanCoupledSourceUnroll_e_eq_sum_sourceCoeff
    (steps : List KahanCoupledCoeffStep) :
    (kahanCoupledSourceUnroll steps).e =
      ∑ i : Fin steps.length,
        (steps.get i).x * (kahanCoupledSourceCoeff steps i).e := by
  induction steps with
  | nil => rfl
  | cons step steps ih =>
      dsimp [kahanCoupledSourceUnroll, KahanState.add]
      change
        (kahanCoupledCoeffPropagate steps step.source).e +
            (kahanCoupledSourceUnroll steps).e =
          ∑ i : Fin (steps.length + 1),
            ((step :: steps).get i).x *
              (kahanCoupledSourceCoeff (step :: steps) i).e
      conv_rhs => rw [Fin.sum_univ_succ]
      rw [ih]
      have hprop :
          kahanCoupledCoeffPropagate steps step.source =
            KahanState.smul step.x
              (kahanCoupledCoeffPropagate steps step.sourceCoeff) := by
        rw [KahanCoupledCoeffStep.source_eq_smul_sourceCoeff]
        exact kahanCoupledCoeffPropagate_smul
          steps step.x step.sourceCoeff
      rw [hprop]
      simp [kahanCoupledSourceCoeff, KahanState.smul]

/-- Paired source coefficient for the compensated total `s+e`.  In the
Goldberg/Knuth route this is the coefficient of the cancellation-preserving
quantity corresponding to `S-C` once the sign convention for the retained
correction is translated to Higham's Algorithm 4.2. -/
noncomputable def kahanCoupledSourceTotalCoeff
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) : ℝ :=
  (kahanCoupledSourceCoeff steps i).s +
    (kahanCoupledSourceCoeff steps i).e

/-- For an original input index, appending Goldberg's phantom exact zero-input
step makes the new returned-sum coefficient equal to the old compensated-total
coefficient. -/
theorem kahanCoupledSourceCoeff_append_exactZeroStep_s_eq_sourceTotalCoeff
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) :
    (kahanCoupledSourceCoeff (steps ++ [kahanCoupledExactZeroStep])
      ⟨i.val, by
        simp [List.length_append]⟩).s =
      kahanCoupledSourceTotalCoeff steps i := by
  dsimp [kahanCoupledSourceCoeff, kahanCoupledSourceTotalCoeff]
  have hle : i.val + 1 ≤ steps.length := Nat.succ_le_of_lt i.isLt
  rw [List.drop_append_of_le_length hle]
  simp [kahanCoupledCoeffPropagate_append_exactZeroStep]

/-- For an original input index, appending Goldberg's phantom exact zero-input
step leaves zero retained-correction coefficient in the appended recurrence. -/
theorem kahanCoupledSourceCoeff_append_exactZeroStep_e_eq_zero
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) :
    (kahanCoupledSourceCoeff (steps ++ [kahanCoupledExactZeroStep])
      ⟨i.val, by
        simp [List.length_append]⟩).e = 0 := by
  dsimp [kahanCoupledSourceCoeff]
  have hle : i.val + 1 ≤ steps.length := Nat.succ_le_of_lt i.isLt
  rw [List.drop_append_of_le_length hle]
  simp [kahanCoupledCoeffPropagate_append_exactZeroStep]

/-- The `s` field of the paired-coordinate source coefficient is the
compensated-total source coefficient. -/
theorem kahanCoupledSourceTotalCorrectionCoeff_s
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) :
    (kahanCoupledSourceTotalCorrectionCoeff steps i).s =
      kahanCoupledSourceTotalCoeff steps i := by
  rfl

/-- The `e` field of the paired-coordinate source coefficient is the retained
correction source coefficient. -/
theorem kahanCoupledSourceTotalCorrectionCoeff_e
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) :
    (kahanCoupledSourceTotalCorrectionCoeff steps i).e =
      (kahanCoupledSourceCoeff steps i).e := by
  rfl

/-- The compensated-total source coefficient is the total component of the
transformed propagated source recurrence. -/
theorem kahanCoupledSourceTotalCoeff_eq_totalCorrectionPropagate_s
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) :
    kahanCoupledSourceTotalCoeff steps i =
      (kahanCoupledTotalCorrectionPropagate
        (steps.drop (i.val + 1))
        (KahanState.totalCorrection (steps.get i).sourceCoeff)).s := by
  rw [← kahanCoupledSourceTotalCorrectionCoeff_s]
  rw [kahanCoupledSourceCoeff_totalCorrection_eq]

/-- The retained-correction source coefficient is the correction component of
the transformed propagated source recurrence. -/
theorem kahanCoupledSourceCoeff_e_eq_totalCorrectionPropagate_e
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) :
    (kahanCoupledSourceCoeff steps i).e =
      (kahanCoupledTotalCorrectionPropagate
        (steps.drop (i.val + 1))
        (KahanState.totalCorrection (steps.get i).sourceCoeff)).e := by
  rw [← kahanCoupledSourceTotalCorrectionCoeff_e]
  rw [kahanCoupledSourceCoeff_totalCorrection_eq]

/-- The returned stored-sum source coefficient is the returned coordinate of
the paired-coordinate propagated source coefficient.

This is the exact bridge from the paired `(s+e,e)` propagation recurrence to
the ordinary returned coefficient needed for Higham equation (4.8). -/
theorem kahanCoupledSourceCoeff_s_eq_returned_totalCorrectionPropagate
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) :
    (kahanCoupledSourceCoeff steps i).s =
      KahanState.returnedFromTotalCorrection
        (kahanCoupledTotalCorrectionPropagate
          (steps.drop (i.val + 1))
          (KahanState.totalCorrection (steps.get i).sourceCoeff)) := by
  rw [← kahanCoupledSourceCoeff_totalCorrection_eq steps i]
  dsimp [kahanCoupledSourceTotalCorrectionCoeff]
  exact (KahanState.returnedFromTotalCorrection_totalCorrection
    (kahanCoupledSourceCoeff steps i)).symm

/-- Compensated-total component of the coupled source-vector unroll as an
explicit per-input paired-coefficient sum. -/
theorem kahanCoupledSourceUnroll_total_eq_sum_sourceTotalCoeff
    (steps : List KahanCoupledCoeffStep) :
    (kahanCoupledSourceUnroll steps).s +
        (kahanCoupledSourceUnroll steps).e =
      ∑ i : Fin steps.length,
        (steps.get i).x * kahanCoupledSourceTotalCoeff steps i := by
  rw [kahanCoupledSourceUnroll_s_eq_sum_sourceCoeff,
    kahanCoupledSourceUnroll_e_eq_sum_sourceCoeff]
  calc
    (∑ i : Fin steps.length,
        (steps.get i).x * (kahanCoupledSourceCoeff steps i).s) +
        (∑ i : Fin steps.length,
          (steps.get i).x * (kahanCoupledSourceCoeff steps i).e) =
      ∑ i : Fin steps.length,
        ((steps.get i).x * (kahanCoupledSourceCoeff steps i).s +
          (steps.get i).x * (kahanCoupledSourceCoeff steps i).e) := by
        rw [Finset.sum_add_distrib]
    _ = ∑ i : Fin steps.length,
        (steps.get i).x * kahanCoupledSourceTotalCoeff steps i := by
        apply Finset.sum_congr rfl
        intro i _hi
        dsimp [kahanCoupledSourceTotalCoeff]
        ring

/-- The coupled direct coefficient step induced by one indexed Kahan
prefix-trace step, using an explicit roundoff-witness bundle.

This witness-parametric surface is the exact-subtraction route for Higham
equation (4.8): later finite-format work can provide witnesses whose
correction-subtraction delta is definitionally zero, instead of relying on the
arbitrary `Classical.choice` witness used by `kahanTrace_deltaWitness`. -/
def kahanCoupledCoeffStepOfWitness
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))) :
    KahanCoupledCoeffStep :=
  { A := kahanStoredSumStateCoeff w.deltaS
    B := kahanStoredSumInputCoeff w.deltaY w.deltaS
    C := kahanCorrectionStateCoeff w.deltaS w.deltaSub w.deltaE
    D := kahanCorrectionInputCoeff w.deltaY w.deltaS w.deltaSub w.deltaE
    x := v i }

/-- The explicit-witness coupled step's total old-state coefficient is the
named compensated-total old-state coefficient. -/
theorem kahanCoupledCoeffStepOfWitness_totalStateCoeff_eq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))) :
    (kahanCoupledCoeffStepOfWitness fp v i w).totalStateCoeff =
      kahanTotalStateCoeff w.deltaS w.deltaSub w.deltaE := by
  dsimp [kahanCoupledCoeffStepOfWitness,
    KahanCoupledCoeffStep.totalStateCoeff,
    kahanStoredSumStateCoeff, kahanCorrectionStateCoeff,
    kahanTotalStateCoeff]
  ring

/-- The explicit-witness coupled step's total current-input coefficient is the
named compensated-total current-input coefficient. -/
theorem kahanCoupledCoeffStepOfWitness_totalInputCoeff_eq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))) :
    (kahanCoupledCoeffStepOfWitness fp v i w).totalInputCoeff =
      kahanTotalInputCoeff w.deltaY w.deltaS w.deltaSub w.deltaE := by
  dsimp [kahanCoupledCoeffStepOfWitness,
    KahanCoupledCoeffStep.totalInputCoeff,
    kahanStoredSumInputCoeff, kahanCorrectionInputCoeff,
    kahanTotalInputCoeff]
  ring

/-- The explicit-witness coupled step's paired-total residual coefficient is
the named Kahan total residual coefficient. -/
theorem kahanCoupledCoeffStepOfWitness_residualCoeff_eq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))) :
    (kahanCoupledCoeffStepOfWitness fp v i w).residualCoeff =
      kahanTotalResidualCoeff w.deltaY w.deltaS w.deltaSub w.deltaE := by
  rw [KahanCoupledCoeffStep.residualCoeff,
    kahanCoupledCoeffStepOfWitness_totalInputCoeff_eq,
    kahanCoupledCoeffStepOfWitness_totalStateCoeff_eq]
  rfl

/-- General explicit-witness correction-residual cancellation: the coupled
correction residual differs from `-deltaSub` only by a second-order local
remainder. -/
theorem kahanCoupledCoeffStepOfWitness_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)))
    (hu1 : fp.u ≤ 1) :
    |(kahanCoupledCoeffStepOfWitness fp v i w).correctionResidualCoeff +
        w.deltaSub| ≤
      7 * fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfWitness,
    KahanCoupledCoeffStep.correctionResidualCoeff] using
    kahanCorrectionInputCoeff_sub_stateCoeff_add_deltaSub_abs_le_seven_u_sq
      (deltaY := w.deltaY) (deltaS := w.deltaS)
      (deltaSub := w.deltaSub) (deltaE := w.deltaE)
      (u := fp.u) fp.u_nonneg hu1 w.h_deltaY w.h_deltaS
      w.h_deltaSub w.h_deltaE

/-- General explicit-witness relation between the paired-total residual and
the correction residual: their difference is `deltaY + O(u^2)`. -/
theorem kahanCoupledCoeffStepOfWitness_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))) :
    |(kahanCoupledCoeffStepOfWitness fp v i w).residualCoeff -
        (kahanCoupledCoeffStepOfWitness fp v i w).correctionResidualCoeff -
        w.deltaY| ≤
      fp.u ^ 2 := by
  have hrewrite :
      (kahanCoupledCoeffStepOfWitness fp v i w).residualCoeff -
          (kahanCoupledCoeffStepOfWitness fp v i w).correctionResidualCoeff -
          w.deltaY =
        w.deltaY * w.deltaS := by
    dsimp [kahanCoupledCoeffStepOfWitness,
      KahanCoupledCoeffStep.residualCoeff,
      KahanCoupledCoeffStep.correctionResidualCoeff,
      KahanCoupledCoeffStep.totalInputCoeff,
      KahanCoupledCoeffStep.totalStateCoeff,
      kahanStoredSumInputCoeff, kahanStoredSumStateCoeff]
    ring
  rw [hrewrite]
  calc
    |w.deltaY * w.deltaS| = |w.deltaY| * |w.deltaS| := by rw [abs_mul]
    _ ≤ fp.u * fp.u :=
      mul_le_mul w.h_deltaY w.h_deltaS (abs_nonneg _) fp.u_nonneg
    _ = fp.u ^ 2 := by ring

/-- General explicit-witness combined residual cancellation: the paired-total
residual is `deltaY - deltaSub` up to a second-order local remainder. -/
theorem kahanCoupledCoeffStepOfWitness_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)))
    (hu1 : fp.u ≤ 1) :
    |(kahanCoupledCoeffStepOfWitness fp v i w).residualCoeff +
        w.deltaSub - w.deltaY| ≤
      8 * fp.u ^ 2 := by
  rw [kahanCoupledCoeffStepOfWitness_residualCoeff_eq]
  exact
    kahanTotalResidualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq
      (deltaY := w.deltaY) (deltaS := w.deltaS)
      (deltaSub := w.deltaSub) (deltaE := w.deltaE)
      (u := fp.u) fp.u_nonneg hu1 w.h_deltaY w.h_deltaS
      w.h_deltaSub w.h_deltaE

/-- Exact-subtraction local bound for an explicit-witness coupled Kahan step's
paired-total old-state coefficient. -/
theorem kahanCoupledCoeffStepOfWitness_totalStateCoeff_abs_sub_one_le_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)))
    (hSubZero : w.deltaSub = 0) :
    |(kahanCoupledCoeffStepOfWitness fp v i w).totalStateCoeff - 1| ≤
      fp.u ^ 2 := by
  rw [kahanCoupledCoeffStepOfWitness_totalStateCoeff_eq, hSubZero]
  exact
    kahanTotalStateCoeff_abs_sub_one_le_u_sq_of_deltaSub_zero
      (deltaS := w.deltaS) (deltaE := w.deltaE)
      (u := fp.u) fp.u_nonneg w.h_deltaS w.h_deltaE

/-- Exact-subtraction local bound for an explicit-witness coupled Kahan step's
paired-total current-input coefficient. -/
theorem kahanCoupledCoeffStepOfWitness_totalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)))
    (hu1 : fp.u ≤ 1) (hSubZero : w.deltaSub = 0) :
    |(kahanCoupledCoeffStepOfWitness fp v i w).totalInputCoeff - 1| ≤
      fp.u + 2 * fp.u ^ 2 := by
  rw [kahanCoupledCoeffStepOfWitness_totalInputCoeff_eq, hSubZero]
  exact
    kahanTotalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_deltaSub_zero
      (deltaY := w.deltaY) (deltaS := w.deltaS) (deltaE := w.deltaE)
      (u := fp.u) fp.u_nonneg hu1 w.h_deltaY w.h_deltaS w.h_deltaE

/-- Exact-subtraction local bound for an explicit-witness coupled Kahan step's
paired-total retained-correction residual. -/
theorem kahanCoupledCoeffStepOfWitness_residualCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)))
    (hu1 : fp.u ≤ 1) (hSubZero : w.deltaSub = 0) :
    |(kahanCoupledCoeffStepOfWitness fp v i w).residualCoeff| ≤
      fp.u + fp.u ^ 2 := by
  rw [kahanCoupledCoeffStepOfWitness_residualCoeff_eq, hSubZero]
  exact
    kahanTotalResidualCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero
      (deltaY := w.deltaY) (deltaS := w.deltaS) (deltaE := w.deltaE)
      (u := fp.u) fp.u_nonneg hu1 w.h_deltaY w.h_deltaS w.h_deltaE

/-- Exact-subtraction local bound for an explicit-witness coupled Kahan step's
correction old-total coefficient. -/
theorem kahanCoupledCoeffStepOfWitness_C_abs_le_u_plus_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)))
    (hSubZero : w.deltaSub = 0) :
    |(kahanCoupledCoeffStepOfWitness fp v i w).C| ≤
      fp.u + fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfWitness, hSubZero] using
    kahanCorrectionStateCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero
      (deltaS := w.deltaS) (deltaE := w.deltaE)
      (u := fp.u) fp.u_nonneg w.h_deltaS w.h_deltaE

/-- Exact-subtraction local bound for an explicit-witness coupled Kahan step's
correction current-input coefficient. -/
theorem kahanCoupledCoeffStepOfWitness_D_abs_le_u_plus_three_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)))
    (hu1 : fp.u ≤ 1) (hSubZero : w.deltaSub = 0) :
    |(kahanCoupledCoeffStepOfWitness fp v i w).D| ≤
      fp.u + 3 * fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfWitness, hSubZero] using
    kahanCorrectionInputCoeff_abs_le_u_plus_three_u_sq_of_deltaSub_zero
      (deltaY := w.deltaY) (deltaS := w.deltaS) (deltaE := w.deltaE)
      (u := fp.u) fp.u_nonneg hu1 w.h_deltaY w.h_deltaS w.h_deltaE

/-- Exact-subtraction local bound for an explicit-witness coupled Kahan step's
paired correction residual. -/
theorem kahanCoupledCoeffStepOfWitness_correctionResidualCoeff_abs_le_two_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)))
    (hu1 : fp.u ≤ 1) (hSubZero : w.deltaSub = 0) :
    |(kahanCoupledCoeffStepOfWitness fp v i w).correctionResidualCoeff| ≤
      2 * fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfWitness,
    KahanCoupledCoeffStep.correctionResidualCoeff, hSubZero] using
    kahanCorrectionResidualCoeff_abs_le_two_u_sq_of_deltaSub_zero
      (deltaY := w.deltaY) (deltaS := w.deltaS) (deltaE := w.deltaE)
      (u := fp.u) fp.u_nonneg hu1 w.h_deltaY w.h_deltaS w.h_deltaE

/-- One indexed Kahan prefix-trace step satisfies the coupled direct
stored-sum/correction coefficient recurrence for any valid explicit
roundoff-witness bundle. -/
theorem kahanTrace_eq_coupledCoeffStepOfWitness_next
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    let step := kahanCoupledCoeffStepOfWitness fp v i w
    (kahanTrace fp v i).nextState = step.next state := by
  have hs :=
    kahanStepDeltaWitness_s_coefficients fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)) w
  have he :=
    kahanStepDeltaWitness_e_coefficients fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)) w
  dsimp [KahanStepTrace.nextState, KahanCoupledCoeffStep.next,
    kahanCoupledCoeffStepOfWitness, kahanTrace]
  rw [hs, he]

/-- The coupled direct coefficient step induced by one indexed Kahan
prefix-trace step. -/
noncomputable def kahanCoupledCoeffStepOfIndex
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    KahanCoupledCoeffStep :=
  let w := kahanTrace_deltaWitness fp v i
  { A := kahanStoredSumStateCoeff w.deltaS
    B := kahanStoredSumInputCoeff w.deltaY w.deltaS
    C := kahanCorrectionStateCoeff w.deltaS w.deltaSub w.deltaE
    D := kahanCorrectionInputCoeff w.deltaY w.deltaS w.deltaSub w.deltaE
    x := v i }

/-- The coupled step's total old-state coefficient is the already named
compensated-total old-state coefficient. -/
theorem kahanCoupledCoeffStepOfIndex_totalStateCoeff_eq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    (kahanCoupledCoeffStepOfIndex fp v i).totalStateCoeff =
      kahanTotalStateCoeff
        (kahanTrace_deltaWitness fp v i).deltaS
        (kahanTrace_deltaWitness fp v i).deltaSub
        (kahanTrace_deltaWitness fp v i).deltaE := by
  dsimp [kahanCoupledCoeffStepOfIndex,
    KahanCoupledCoeffStep.totalStateCoeff,
    kahanStoredSumStateCoeff, kahanCorrectionStateCoeff,
    kahanTotalStateCoeff]
  ring

/-- The coupled step's total current-input coefficient is the already named
compensated-total current-input coefficient. -/
theorem kahanCoupledCoeffStepOfIndex_totalInputCoeff_eq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    (kahanCoupledCoeffStepOfIndex fp v i).totalInputCoeff =
      kahanTotalInputCoeff
        (kahanTrace_deltaWitness fp v i).deltaY
        (kahanTrace_deltaWitness fp v i).deltaS
        (kahanTrace_deltaWitness fp v i).deltaSub
        (kahanTrace_deltaWitness fp v i).deltaE := by
  dsimp [kahanCoupledCoeffStepOfIndex,
    KahanCoupledCoeffStep.totalInputCoeff,
    kahanStoredSumInputCoeff, kahanCorrectionInputCoeff,
    kahanTotalInputCoeff]
  ring

/-- The coupled step's total residual coefficient is the retained-correction
residual coefficient already used by the residual-aware affine route. -/
theorem kahanCoupledCoeffStepOfIndex_residualCoeff_eq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    (kahanCoupledCoeffStepOfIndex fp v i).residualCoeff =
      kahanTotalResidualCoeff
        (kahanTrace_deltaWitness fp v i).deltaY
        (kahanTrace_deltaWitness fp v i).deltaS
        (kahanTrace_deltaWitness fp v i).deltaSub
        (kahanTrace_deltaWitness fp v i).deltaE := by
  rw [KahanCoupledCoeffStep.residualCoeff,
    kahanCoupledCoeffStepOfIndex_totalInputCoeff_eq,
    kahanCoupledCoeffStepOfIndex_totalStateCoeff_eq]
  rfl

/-- Actual-prefix version of the general correction-residual cancellation:
the paired correction residual differs from the negated subtraction delta only
by a second-order local remainder. -/
theorem kahanCoupledCoeffStepOfIndex_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    |(kahanCoupledCoeffStepOfIndex fp v i).correctionResidualCoeff +
        (kahanTrace_deltaWitness fp v i).deltaSub| ≤
      7 * fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfIndex,
    KahanCoupledCoeffStep.correctionResidualCoeff] using
    kahanCorrectionInputCoeff_sub_stateCoeff_add_deltaSub_abs_le_seven_u_sq
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaSub := (kahanTrace_deltaWitness fp v i).deltaSub)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaSub
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- Actual-prefix relation between the paired-total residual and the
correction residual: their difference is the input-addition delta plus a
second-order local remainder. -/
theorem kahanCoupledCoeffStepOfIndex_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |(kahanCoupledCoeffStepOfIndex fp v i).residualCoeff -
        (kahanCoupledCoeffStepOfIndex fp v i).correctionResidualCoeff -
        (kahanTrace_deltaWitness fp v i).deltaY| ≤
      fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfIndex] using
    kahanCoupledCoeffStepOfWitness_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq
      fp v i (kahanTrace_deltaWitness fp v i)

/-- Actual-prefix combined residual cancellation: the paired-total residual is
`deltaY - deltaSub` up to a second-order local remainder. -/
theorem kahanCoupledCoeffStepOfIndex_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    |(kahanCoupledCoeffStepOfIndex fp v i).residualCoeff +
        (kahanTrace_deltaWitness fp v i).deltaSub -
        (kahanTrace_deltaWitness fp v i).deltaY| ≤
      8 * fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfIndex] using
    kahanCoupledCoeffStepOfWitness_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq
      fp v i (kahanTrace_deltaWitness fp v i) hu1

/-- The total old-state coefficient of an actual coupled Kahan step differs
from one by at most `3*u^2`. -/
theorem kahanCoupledCoeffStepOfIndex_totalStateCoeff_abs_sub_one_le_three_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    |(kahanCoupledCoeffStepOfIndex fp v i).totalStateCoeff - 1| ≤
      3 * fp.u ^ 2 := by
  rw [kahanCoupledCoeffStepOfIndex_totalStateCoeff_eq]
  exact
    kahanTotalStateCoeff_abs_sub_one_le_three_u_sq
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaSub := (kahanTrace_deltaWitness fp v i).deltaSub)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaSub
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- The total current-input coefficient of an actual coupled Kahan step differs
from one by at most `2*u + 9*u^2`. -/
theorem kahanCoupledCoeffStepOfIndex_totalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    |(kahanCoupledCoeffStepOfIndex fp v i).totalInputCoeff - 1| ≤
      2 * fp.u + 9 * fp.u ^ 2 := by
  rw [kahanCoupledCoeffStepOfIndex_totalInputCoeff_eq]
  exact
    kahanTotalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaSub := (kahanTrace_deltaWitness fp v i).deltaSub)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaSub
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- The total residual coefficient of an actual coupled Kahan step satisfies
the same small-`u` residual bound as the affine route. -/
theorem kahanCoupledCoeffStepOfIndex_residualCoeff_abs_le_two_u_plus_twelve_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    |(kahanCoupledCoeffStepOfIndex fp v i).residualCoeff| ≤
      2 * fp.u + 12 * fp.u ^ 2 := by
  rw [kahanCoupledCoeffStepOfIndex_residualCoeff_eq]
  exact
    kahanTotalResidualCoeff_abs_le_two_u_plus_twelve_u_sq
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaSub := (kahanTrace_deltaWitness fp v i).deltaSub)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaSub
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- The correction-total coefficient `C` of an actual coupled Kahan step is
bounded by the existing local retained-correction state coefficient radius. -/
theorem kahanCoupledCoeffStepOfIndex_C_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |(kahanCoupledCoeffStepOfIndex fp v i).C| ≤
      fp.u * (1 + fp.u) ^ 2 := by
  simpa [kahanCoupledCoeffStepOfIndex] using
    kahanCorrectionStateCoeff_abs_le
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaSub := (kahanTrace_deltaWitness fp v i).deltaSub)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaSub
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- The correction-residual input coefficient `D` of an actual coupled Kahan
step is bounded by the existing local retained-correction input coefficient
radius. -/
theorem kahanCoupledCoeffStepOfIndex_D_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |(kahanCoupledCoeffStepOfIndex fp v i).D| ≤
      fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) := by
  simpa [kahanCoupledCoeffStepOfIndex] using
    kahanCorrectionInputCoeff_abs_le
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaSub := (kahanTrace_deltaWitness fp v i).deltaSub)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaSub
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- The correction residual coefficient `D-C` in paired coordinates is bounded
by the sum of the local correction-row coefficient bounds. -/
theorem kahanCoupledCoeffStepOfIndex_correctionResidualCoeff_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |(kahanCoupledCoeffStepOfIndex fp v i).correctionResidualCoeff| ≤
      fp.u * (1 + fp.u) ^ 2 * (3 + fp.u) := by
  let step := kahanCoupledCoeffStepOfIndex fp v i
  have hC :
      |step.C| ≤ fp.u * (1 + fp.u) ^ 2 := by
    simpa [step] using kahanCoupledCoeffStepOfIndex_C_abs_le fp v i
  have hD :
      |step.D| ≤ fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) := by
    simpa [step] using kahanCoupledCoeffStepOfIndex_D_abs_le fp v i
  have htri : |step.D - step.C| ≤ |step.D| + |step.C| := by
    simpa [sub_eq_add_neg, abs_neg] using
      abs_add_le step.D (-step.C)
  calc
    |step.correctionResidualCoeff| = |step.D - step.C| := by
      rfl
    _ ≤ |step.D| + |step.C| := htri
    _ ≤ fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) +
          fp.u * (1 + fp.u) ^ 2 := by
        exact add_le_add hD hC
    _ = fp.u * (1 + fp.u) ^ 2 * (3 + fp.u) := by
        ring

/-- Exact-subtraction local bound for an actual coupled Kahan step's
paired-total old-state coefficient. -/
theorem kahanCoupledCoeffStepOfIndex_totalStateCoeff_abs_sub_one_le_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hSubZero : (kahanTrace_deltaWitness fp v i).deltaSub = 0) :
    |(kahanCoupledCoeffStepOfIndex fp v i).totalStateCoeff - 1| ≤
      fp.u ^ 2 := by
  rw [kahanCoupledCoeffStepOfIndex_totalStateCoeff_eq, hSubZero]
  exact
    kahanTotalStateCoeff_abs_sub_one_le_u_sq_of_deltaSub_zero
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- Exact-subtraction local bound for an actual coupled Kahan step's
paired-total current-input coefficient. -/
theorem kahanCoupledCoeffStepOfIndex_totalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1)
    (hSubZero : (kahanTrace_deltaWitness fp v i).deltaSub = 0) :
    |(kahanCoupledCoeffStepOfIndex fp v i).totalInputCoeff - 1| ≤
      fp.u + 2 * fp.u ^ 2 := by
  rw [kahanCoupledCoeffStepOfIndex_totalInputCoeff_eq, hSubZero]
  exact
    kahanTotalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_deltaSub_zero
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- Exact-subtraction local bound for an actual coupled Kahan step's
paired-total retained-correction residual. -/
theorem kahanCoupledCoeffStepOfIndex_residualCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1)
    (hSubZero : (kahanTrace_deltaWitness fp v i).deltaSub = 0) :
    |(kahanCoupledCoeffStepOfIndex fp v i).residualCoeff| ≤
      fp.u + fp.u ^ 2 := by
  rw [kahanCoupledCoeffStepOfIndex_residualCoeff_eq, hSubZero]
  exact
    kahanTotalResidualCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- Exact-subtraction local bound for an actual coupled Kahan step's
correction old-total coefficient. -/
theorem kahanCoupledCoeffStepOfIndex_C_abs_le_u_plus_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hSubZero : (kahanTrace_deltaWitness fp v i).deltaSub = 0) :
    |(kahanCoupledCoeffStepOfIndex fp v i).C| ≤
      fp.u + fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfIndex, hSubZero] using
    kahanCorrectionStateCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- Exact-subtraction local bound for an actual coupled Kahan step's
correction current-input coefficient. -/
theorem kahanCoupledCoeffStepOfIndex_D_abs_le_u_plus_three_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1)
    (hSubZero : (kahanTrace_deltaWitness fp v i).deltaSub = 0) :
    |(kahanCoupledCoeffStepOfIndex fp v i).D| ≤
      fp.u + 3 * fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfIndex, hSubZero] using
    kahanCorrectionInputCoeff_abs_le_u_plus_three_u_sq_of_deltaSub_zero
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- Exact-subtraction local bound for an actual coupled Kahan step's paired
correction residual. -/
theorem kahanCoupledCoeffStepOfIndex_correctionResidualCoeff_abs_le_two_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1)
    (hSubZero : (kahanTrace_deltaWitness fp v i).deltaSub = 0) :
    |(kahanCoupledCoeffStepOfIndex fp v i).correctionResidualCoeff| ≤
      2 * fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfIndex,
    KahanCoupledCoeffStep.correctionResidualCoeff, hSubZero] using
    kahanCorrectionResidualCoeff_abs_le_two_u_sq_of_deltaSub_zero
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- The returned-coordinate old-state coefficient of an actual coupled Kahan
step has only the direct stored-sum first-order radius.  This is the precise
local obstruction that prevents reusing the compensated-total coefficient
collapse for the ordinary returned sum in the bare abstract `FPModel`. -/
theorem kahanCoupledCoeffStepOfIndex_returnedStateCoeff_abs_sub_one_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |(kahanCoupledCoeffStepOfIndex fp v i).returnedStateCoeff - 1| ≤
      fp.u := by
  rw [KahanCoupledCoeffStep.returnedStateCoeff_eq_A]
  simpa [kahanCoupledCoeffStepOfIndex] using
    kahanStoredSumStateCoeff_abs_sub_one_le
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (u := fp.u)
      (kahanTrace_deltaWitness fp v i).h_deltaS

/-- The returned-coordinate retained-correction coefficient of an actual
coupled Kahan step is `O(u)`.  Multiplied by the paired correction coefficient
this term is second order, but the returned old-state coefficient above still
carries the first-order radius. -/
theorem kahanCoupledCoeffStepOfIndex_returnedCorrectionCoeff_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |(kahanCoupledCoeffStepOfIndex fp v i).returnedCorrectionCoeff| ≤
      fp.u * (1 + fp.u) := by
  rw [KahanCoupledCoeffStep.returnedCorrectionCoeff_eq_B_sub_A]
  simpa [kahanCoupledCoeffStepOfIndex] using
    kahanStoredSumInputCoeff_sub_stateCoeff_abs_le_u_mul_one_add_u
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (u := fp.u) fp.u_nonneg
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS

/-- One indexed Kahan prefix-trace step satisfies the coupled direct
stored-sum/correction coefficient recurrence. -/
theorem kahanTrace_eq_coupledCoeffStep_next
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    let step := kahanCoupledCoeffStepOfIndex fp v i
    (kahanTrace fp v i).nextState = step.next state := by
  have hs := kahanTrace_deltaWitness_s_coefficients fp v i
  have he := kahanTrace_deltaWitness_e_coefficients fp v i
  dsimp at hs he
  dsimp [KahanStepTrace.nextState, KahanCoupledCoeffStep.next,
    kahanCoupledCoeffStepOfIndex]
  rw [hs, he]

/-- The concrete coupled coefficient steps for the first `k` Kahan prefix
steps. -/
noncomputable def kahanCoupledCoeffSteps
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    List KahanCoupledCoeffStep :=
  List.ofFn fun i : Fin k =>
    let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    kahanCoupledCoeffStepOfIndex fp v idx

/-- Prefix-level exact-subtraction hypothesis for the chosen Kahan
roundoff-witnesses: every correction subtraction in the first `k` steps has
zero subtraction delta.  This is a local bridge hypothesis, not a consequence
of bare `FPModel`. -/
def kahanCoupledCoeffStepsExactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : Prop :=
  ∀ i : Fin k,
    (kahanTrace_deltaWitness fp v
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩).deltaSub = 0

/-- Every actual coupled coefficient step in the first `k` Kahan prefix steps
has total old-state coefficient within `3*u^2` of one. -/
theorem kahanCoupledCoeffSteps_totalStateCoeff_abs_sub_one_le_three_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.totalStateCoeff - 1| ≤ 3 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_totalStateCoeff_abs_sub_one_le_three_u_sq
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ hu1

/-- Every actual coupled coefficient step in the first `k` Kahan prefix steps
has total current-input coefficient within `2*u + 9*u^2` of one. -/
theorem kahanCoupledCoeffSteps_totalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.totalInputCoeff - 1| ≤ 2 * fp.u + 9 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_totalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ hu1

/-- Every actual coupled coefficient step in the first `k` Kahan prefix steps
has residual coefficient bounded by `2*u + 12*u^2`. -/
theorem kahanCoupledCoeffSteps_residualCoeff_abs_le_two_u_plus_twelve_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.residualCoeff| ≤ 2 * fp.u + 12 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_residualCoeff_abs_le_two_u_plus_twelve_u_sq
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ hu1

/-- Every actual coupled coefficient step in the first `k` Kahan prefix steps
has correction-total coefficient bounded by `u*(1+u)^2`. -/
theorem kahanCoupledCoeffSteps_C_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.C| ≤ fp.u * (1 + fp.u) ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_C_abs_le
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

/-- Every actual coupled coefficient step in the first `k` Kahan prefix steps
has correction-input coefficient bounded by `u*(1+u)^2*(2+u)`. -/
theorem kahanCoupledCoeffSteps_D_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.D| ≤ fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_D_abs_le
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

/-- Every actual coupled coefficient step in the first `k` Kahan prefix steps
has paired-coordinate correction residual coefficient bounded by
`u*(1+u)^2*(3+u)`. -/
theorem kahanCoupledCoeffSteps_correctionResidualCoeff_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.correctionResidualCoeff| ≤
        fp.u * (1 + fp.u) ^ 2 * (3 + fp.u) := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_correctionResidualCoeff_abs_le
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

/-- Prefix-indexed form of the general correction-residual cancellation for
the actual chosen witness used by `kahanCoupledCoeffSteps`. -/
theorem kahanCoupledCoeffSteps_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) :
    ∀ i : Fin k,
      let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
      |(kahanCoupledCoeffStepOfIndex fp v idx).correctionResidualCoeff +
          (kahanTrace_deltaWitness fp v idx).deltaSub| ≤
        7 * fp.u ^ 2 := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfIndex_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq
      fp v idx hu1

/-- Prefix-indexed form of
`residualCoeff - correctionResidualCoeff = deltaY + O(u^2)` for the actual
chosen witness used by `kahanCoupledCoeffSteps`. -/
theorem kahanCoupledCoeffSteps_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∀ i : Fin k,
      let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
      |(kahanCoupledCoeffStepOfIndex fp v idx).residualCoeff -
          (kahanCoupledCoeffStepOfIndex fp v idx).correctionResidualCoeff -
          (kahanTrace_deltaWitness fp v idx).deltaY| ≤
        fp.u ^ 2 := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfIndex_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq
      fp v idx

/-- Prefix-indexed combined residual cancellation for the actual chosen
witness used by `kahanCoupledCoeffSteps`. -/
theorem kahanCoupledCoeffSteps_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) :
    ∀ i : Fin k,
      let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
      |(kahanCoupledCoeffStepOfIndex fp v idx).residualCoeff +
          (kahanTrace_deltaWitness fp v idx).deltaSub -
          (kahanTrace_deltaWitness fp v idx).deltaY| ≤
        8 * fp.u ^ 2 := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfIndex_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq
      fp v idx hu1

/-- Under the prefix exact-subtraction hypothesis, every actual coupled step
has paired-total old-state coefficient within `u^2` of one. -/
theorem kahanCoupledCoeffSteps_totalStateCoeff_abs_sub_one_le_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hExactSub : kahanCoupledCoeffStepsExactSub fp v k hk) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.totalStateCoeff - 1| ≤ fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_totalStateCoeff_abs_sub_one_le_u_sq_of_deltaSub_zero
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ (hExactSub i)

/-- Under the prefix exact-subtraction hypothesis, every actual coupled step
has paired-total current-input coefficient within `u + 2*u^2` of one. -/
theorem kahanCoupledCoeffSteps_totalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (hExactSub : kahanCoupledCoeffStepsExactSub fp v k hk) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.totalInputCoeff - 1| ≤ fp.u + 2 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_totalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_deltaSub_zero
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ hu1 (hExactSub i)

/-- Under the prefix exact-subtraction hypothesis, every actual coupled step
has paired-total retained-correction residual bounded by `u + u^2`. -/
theorem kahanCoupledCoeffSteps_residualCoeff_abs_le_u_plus_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (hExactSub : kahanCoupledCoeffStepsExactSub fp v k hk) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.residualCoeff| ≤ fp.u + fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_residualCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ hu1 (hExactSub i)

/-- Under the prefix exact-subtraction hypothesis, every actual coupled step's
correction old-total coefficient is bounded by `u + u^2`. -/
theorem kahanCoupledCoeffSteps_C_abs_le_u_plus_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hExactSub : kahanCoupledCoeffStepsExactSub fp v k hk) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.C| ≤ fp.u + fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_C_abs_le_u_plus_u_sq_of_deltaSub_zero
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ (hExactSub i)

/-- Under the prefix exact-subtraction hypothesis, every actual coupled step's
correction current-input coefficient is bounded by `u + 3*u^2`. -/
theorem kahanCoupledCoeffSteps_D_abs_le_u_plus_three_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (hExactSub : kahanCoupledCoeffStepsExactSub fp v k hk) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.D| ≤ fp.u + 3 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_D_abs_le_u_plus_three_u_sq_of_deltaSub_zero
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ hu1 (hExactSub i)

/-- Under the prefix exact-subtraction hypothesis, every actual coupled step's
paired correction residual is second order. -/
theorem kahanCoupledCoeffSteps_correctionResidualCoeff_abs_le_two_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (hExactSub : kahanCoupledCoeffStepsExactSub fp v k hk) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.correctionResidualCoeff| ≤ 2 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_correctionResidualCoeff_abs_le_two_u_sq_of_deltaSub_zero
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ hu1 (hExactSub i)

/-- Every actual coupled coefficient step has returned-coordinate old-state
coefficient within first-order radius `u` of one. -/
theorem kahanCoupledCoeffSteps_returnedStateCoeff_abs_sub_one_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.returnedStateCoeff - 1| ≤ fp.u := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_returnedStateCoeff_abs_sub_one_le
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

/-- Every actual coupled coefficient step has returned-coordinate retained
correction coefficient bounded by `u*(1+u)`. -/
theorem kahanCoupledCoeffSteps_returnedCorrectionCoeff_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.returnedCorrectionCoeff| ≤ fp.u * (1 + fp.u) := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_returnedCorrectionCoeff_abs_le
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

/-- One-step paired-coordinate total-deviation inequality for every concrete
Kahan prefix coefficient step.  This is the local recurrence inequality needed
by the next Goldberg-style paired coefficient induction. -/
theorem kahanCoupledCoeffSteps_propagateTotalCorrection_totalDev_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk, ∀ state : KahanState,
      |(step.propagateTotalCorrection state).s - 1| ≤
        |state.s - 1| * (1 + 3 * fp.u ^ 2) +
          3 * fp.u ^ 2 +
          |state.e| * (2 * fp.u + 12 * fp.u ^ 2) := by
  intro step hmem state
  exact
    KahanCoupledCoeffStep.propagateTotalCorrection_totalDev_abs_le_of_bounds
      step state
      (eta := 3 * fp.u ^ 2)
      (rho := 2 * fp.u + 12 * fp.u ^ 2)
      (kahanCoupledCoeffSteps_totalStateCoeff_abs_sub_one_le_three_u_sq
        fp v k hk hu1 step hmem)
      (kahanCoupledCoeffSteps_residualCoeff_abs_le_two_u_plus_twelve_u_sq
        fp v k hk hu1 step hmem)

/-- One-step paired-coordinate retained-correction inequality for every
concrete Kahan prefix coefficient step. -/
theorem kahanCoupledCoeffSteps_propagateTotalCorrection_correction_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk, ∀ state : KahanState,
      |(step.propagateTotalCorrection state).e| ≤
        (|state.s - 1| + 1) * (fp.u * (1 + fp.u) ^ 2) +
          |state.e| * (fp.u * (1 + fp.u) ^ 2 * (3 + fp.u)) := by
  intro step hmem state
  exact
    KahanCoupledCoeffStep.propagateTotalCorrection_correction_abs_le_of_bounds
      step state
      (sigma := fp.u * (1 + fp.u) ^ 2)
      (chi := fp.u * (1 + fp.u) ^ 2 * (3 + fp.u))
      (kahanCoupledCoeffSteps_C_abs_le fp v k hk step hmem)
      (kahanCoupledCoeffSteps_correctionResidualCoeff_abs_le
        fp v k hk step hmem)

/-- Exact-subtraction version of the one-step paired-coordinate total
deviation inequality for concrete Kahan prefix coefficient steps. -/
theorem kahanCoupledCoeffSteps_propagateTotalCorrection_totalDev_abs_le_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (hExactSub : kahanCoupledCoeffStepsExactSub fp v k hk) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk, ∀ state : KahanState,
      |(step.propagateTotalCorrection state).s - 1| ≤
        |state.s - 1| * (1 + fp.u ^ 2) +
          fp.u ^ 2 +
          |state.e| * (fp.u + fp.u ^ 2) := by
  intro step hmem state
  exact
    KahanCoupledCoeffStep.propagateTotalCorrection_totalDev_abs_le_of_bounds
      step state
      (eta := fp.u ^ 2)
      (rho := fp.u + fp.u ^ 2)
      (kahanCoupledCoeffSteps_totalStateCoeff_abs_sub_one_le_u_sq_of_exactSub
        fp v k hk hExactSub step hmem)
      (kahanCoupledCoeffSteps_residualCoeff_abs_le_u_plus_u_sq_of_exactSub
        fp v k hk hu1 hExactSub step hmem)

/-- Exact-subtraction version of the one-step paired-coordinate retained
correction inequality for concrete Kahan prefix coefficient steps. -/
theorem kahanCoupledCoeffSteps_propagateTotalCorrection_correction_abs_le_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (hExactSub : kahanCoupledCoeffStepsExactSub fp v k hk) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk, ∀ state : KahanState,
      |(step.propagateTotalCorrection state).e| ≤
        (|state.s - 1| + 1) * (fp.u + fp.u ^ 2) +
          |state.e| * (2 * fp.u ^ 2) := by
  intro step hmem state
  exact
    KahanCoupledCoeffStep.propagateTotalCorrection_correction_abs_le_of_bounds
      step state
      (sigma := fp.u + fp.u ^ 2)
      (chi := 2 * fp.u ^ 2)
      (kahanCoupledCoeffSteps_C_abs_le_u_plus_u_sq_of_exactSub
        fp v k hk hExactSub step hmem)
      (kahanCoupledCoeffSteps_correctionResidualCoeff_abs_le_two_u_sq_of_exactSub
        fp v k hk hu1 hExactSub step hmem)

/-- One-step returned-coordinate deviation inequality for every concrete
Kahan prefix coefficient step.  Its old-state term uses `1 + fp.u`, not
`1 + O(fp.u^2)`, which records the exact gap left by the current abstract
coefficient route for Higham equation (4.8). -/
theorem kahanCoupledCoeffSteps_propagateTotalCorrection_returnedDev_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk, ∀ state : KahanState,
      |KahanState.returnedFromTotalCorrection
          (step.propagateTotalCorrection state) - 1| ≤
        |state.s - 1| * (1 + fp.u) + fp.u +
          |state.e| * (fp.u * (1 + fp.u)) := by
  intro step hmem state
  exact
    KahanCoupledCoeffStep.propagateTotalCorrection_returnedDev_abs_le_of_bounds
      step state
      (eta := fp.u)
      (theta := fp.u * (1 + fp.u))
      (kahanCoupledCoeffSteps_returnedStateCoeff_abs_sub_one_le
        fp v k hk step hmem)
      (kahanCoupledCoeffSteps_returnedCorrectionCoeff_abs_le
        fp v k hk step hmem)

/-- Concrete Kahan prefix instance of the paired-coordinate majorant
recurrence.  It bounds propagation through the first `k` Kahan coupled
coefficient steps using the local total/residual and correction-row bounds. -/
theorem kahanCoupledCoeffSteps_totalCorrectionPropagate_abs_le_pairedCoeffMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) (init : KahanState) {S E : ℝ}
    (hS0 : |init.s - 1| ≤ S) (hE0 : |init.e| ≤ E)
    (hS_nonneg : 0 ≤ S) (hE_nonneg : 0 ≤ E) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    let eta := 3 * fp.u ^ 2
    let rho := 2 * fp.u + 12 * fp.u ^ 2
    let sigma := fp.u * (1 + fp.u) ^ 2
    let chi := fp.u * (1 + fp.u) ^ 2 * (3 + fp.u)
    |(kahanCoupledTotalCorrectionPropagate steps init).s - 1| ≤
        (kahanCoupledPairedCoeffMajorant eta rho sigma chi steps S E).s ∧
      |(kahanCoupledTotalCorrectionPropagate steps init).e| ≤
        (kahanCoupledPairedCoeffMajorant eta rho sigma chi steps S E).e := by
  dsimp
  let eta := 3 * fp.u ^ 2
  let rho := 2 * fp.u + 12 * fp.u ^ 2
  let sigma := fp.u * (1 + fp.u) ^ 2
  let chi := fp.u * (1 + fp.u) ^ 2 * (3 + fp.u)
  let steps := kahanCoupledCoeffSteps fp v k hk
  have heta : 0 ≤ eta := by
    dsimp [eta]
    nlinarith [sq_nonneg fp.u]
  have hOneEta : 0 ≤ 1 + eta := by
    nlinarith
  have hrho : 0 ≤ rho := by
    dsimp [rho]
    nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  have hsigma : 0 ≤ sigma := by
    dsimp [sigma]
    exact mul_nonneg fp.u_nonneg (sq_nonneg (1 + fp.u))
  have hchi : 0 ≤ chi := by
    dsimp [chi]
    exact mul_nonneg hsigma (by nlinarith [fp.u_nonneg])
  have hTotal :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).s - 1| ≤
          |state.s - 1| * (1 + eta) + eta + |state.e| * rho := by
    intro step hmem state
    simpa [steps, eta, rho] using
      kahanCoupledCoeffSteps_propagateTotalCorrection_totalDev_abs_le
        fp v k hk hu1 step hmem state
  have hCorrection :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).e| ≤
          (|state.s - 1| + 1) * sigma + |state.e| * chi := by
    intro step hmem state
    simpa [steps, sigma, chi] using
      kahanCoupledCoeffSteps_propagateTotalCorrection_correction_abs_le
        fp v k hk step hmem state
  exact
    kahanCoupledTotalCorrectionPropagate_abs_le_pairedCoeffMajorant
      (eta := eta) (rho := rho) (sigma := sigma) (chi := chi)
      heta hOneEta hrho hsigma hchi steps init
      hS0 hE0 hS_nonneg hE_nonneg hTotal hCorrection

/-- Concrete paired-majorant bound for every propagated source coefficient in
the first `k` Kahan prefix steps.  The suffix majorant starts from the local
current-source total coefficient radius and the local retained-correction
source coefficient bound. -/
theorem kahanCoupledCoeffSteps_sourceTotalCorrectionCoeff_abs_le_pairedCoeffMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (i : Fin (kahanCoupledCoeffSteps fp v k hk).length) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    let eta := 3 * fp.u ^ 2
    let rho := 2 * fp.u + 12 * fp.u ^ 2
    let sigma := fp.u * (1 + fp.u) ^ 2
    let chi := fp.u * (1 + fp.u) ^ 2 * (3 + fp.u)
    let sourceDev := 2 * fp.u + 9 * fp.u ^ 2
    let sourceCorrection := fp.u * (1 + fp.u) ^ 2 * (2 + fp.u)
    |(kahanCoupledSourceTotalCorrectionCoeff steps i).s - 1| ≤
        (kahanCoupledPairedCoeffMajorant eta rho sigma chi
          (steps.drop (i.val + 1)) sourceDev sourceCorrection).s ∧
      |(kahanCoupledSourceTotalCorrectionCoeff steps i).e| ≤
        (kahanCoupledPairedCoeffMajorant eta rho sigma chi
          (steps.drop (i.val + 1)) sourceDev sourceCorrection).e := by
  dsimp
  let steps := kahanCoupledCoeffSteps fp v k hk
  let eta := 3 * fp.u ^ 2
  let rho := 2 * fp.u + 12 * fp.u ^ 2
  let sigma := fp.u * (1 + fp.u) ^ 2
  let chi := fp.u * (1 + fp.u) ^ 2 * (3 + fp.u)
  let sourceDev := 2 * fp.u + 9 * fp.u ^ 2
  let sourceCorrection := fp.u * (1 + fp.u) ^ 2 * (2 + fp.u)
  have heta : 0 ≤ eta := by
    dsimp [eta]
    nlinarith [sq_nonneg fp.u]
  have hOneEta : 0 ≤ 1 + eta := by
    nlinarith
  have hrho : 0 ≤ rho := by
    dsimp [rho]
    nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  have hsigma : 0 ≤ sigma := by
    dsimp [sigma]
    exact mul_nonneg fp.u_nonneg (sq_nonneg (1 + fp.u))
  have hchi : 0 ≤ chi := by
    dsimp [chi]
    exact mul_nonneg hsigma (by nlinarith [fp.u_nonneg])
  have hsourceDev_nonneg : 0 ≤ sourceDev := by
    dsimp [sourceDev]
    nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  have hsourceCorrection_nonneg : 0 ≤ sourceCorrection := by
    dsimp [sourceCorrection]
    exact mul_nonneg hsigma (by nlinarith [fp.u_nonneg])
  have hmem : steps.get i ∈ steps := List.get_mem steps i
  have hS0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).s - 1| ≤
        sourceDev := by
    have h :=
      kahanCoupledCoeffSteps_totalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
        fp v k hk hu1 (steps.get i) hmem
    simpa [steps, sourceDev, KahanState.totalCorrection,
      KahanCoupledCoeffStep.sourceCoeff,
      KahanCoupledCoeffStep.totalInputCoeff] using h
  have hE0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).e| ≤
        sourceCorrection := by
    have h :=
      kahanCoupledCoeffSteps_D_abs_le fp v k hk (steps.get i) hmem
    simpa [steps, sourceCorrection, KahanState.totalCorrection,
      KahanCoupledCoeffStep.sourceCoeff] using h
  have hTotal :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).s - 1| ≤
          |state.s - 1| * (1 + eta) + eta + |state.e| * rho := by
    intro step hstep state
    simpa [steps, eta, rho] using
      kahanCoupledCoeffSteps_propagateTotalCorrection_totalDev_abs_le
        fp v k hk hu1 step hstep state
  have hCorrection :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).e| ≤
          (|state.s - 1| + 1) * sigma + |state.e| * chi := by
    intro step hstep state
    simpa [steps, sigma, chi] using
      kahanCoupledCoeffSteps_propagateTotalCorrection_correction_abs_le
        fp v k hk step hstep state
  exact
    kahanCoupledSourceTotalCorrectionCoeff_abs_le_pairedCoeffMajorant
      (eta := eta) (rho := rho) (sigma := sigma) (chi := chi)
      heta hOneEta hrho hsigma hchi steps i
      hS0 hE0 hsourceDev_nonneg hsourceCorrection_nonneg
      hTotal hCorrection

/-- Concrete Kahan instance of the triangle-route returned-coefficient bound.

The right-hand side is the paired-total majorant plus the paired correction
majorant.  This formalizes the route that is too weak for Higham equation
(4.8), because the retained-correction majorant contributes a first-order
term. -/
theorem kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_pairedCoeffMajorant_sum
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (i : Fin (kahanCoupledCoeffSteps fp v k hk).length) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    let eta := 3 * fp.u ^ 2
    let rho := 2 * fp.u + 12 * fp.u ^ 2
    let sigma := fp.u * (1 + fp.u) ^ 2
    let chi := fp.u * (1 + fp.u) ^ 2 * (3 + fp.u)
    let sourceDev := 2 * fp.u + 9 * fp.u ^ 2
    let sourceCorrection := fp.u * (1 + fp.u) ^ 2 * (2 + fp.u)
    |(kahanCoupledSourceCoeff steps i).s - 1| ≤
      (kahanCoupledPairedCoeffMajorant eta rho sigma chi
        (steps.drop (i.val + 1)) sourceDev sourceCorrection).s +
      (kahanCoupledPairedCoeffMajorant eta rho sigma chi
        (steps.drop (i.val + 1)) sourceDev sourceCorrection).e := by
  dsimp
  let steps := kahanCoupledCoeffSteps fp v k hk
  let eta := 3 * fp.u ^ 2
  let rho := 2 * fp.u + 12 * fp.u ^ 2
  let sigma := fp.u * (1 + fp.u) ^ 2
  let chi := fp.u * (1 + fp.u) ^ 2 * (3 + fp.u)
  let sourceDev := 2 * fp.u + 9 * fp.u ^ 2
  let sourceCorrection := fp.u * (1 + fp.u) ^ 2 * (2 + fp.u)
  have hpair :=
    kahanCoupledCoeffSteps_sourceTotalCorrectionCoeff_abs_le_pairedCoeffMajorant
      fp v k hk hu1 i
  let a := kahanCoupledSourceCoeff steps i
  have htri :
      |a.s - 1| ≤
        |(KahanState.totalCorrection a).s - 1| +
          |(KahanState.totalCorrection a).e| := by
    have hrewrite :
        a.s - 1 = (a.s + a.e - 1) - a.e := by ring
    rw [hrewrite]
    simpa [KahanState.totalCorrection, sub_eq_add_neg, abs_neg] using
      abs_add_le (a.s + a.e - 1) (-a.e)
  exact htri.trans (add_le_add hpair.1 hpair.2)

/-- Conditional returned-source coefficient collapse for ordinary Kahan under
the prefix exact-subtraction hypothesis.

This is the source-shaped theorem needed by Higham equation (4.8), except that
it still assumes the correction-subtraction deltas selected by
`kahanTrace_deltaWitness` are zero.  The remaining finite-format task is to
derive `kahanCoupledCoeffStepsExactSub` from the concrete correction-formula
exactness hypotheses rather than from bare `FPModel`. -/
theorem kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_two_u_plus_exactSubMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (huSmall : fp.u ≤ 1 / 64)
    (hExactSub : kahanCoupledCoeffStepsExactSub fp v k hk)
    (i : Fin (kahanCoupledCoeffSteps fp v k hk).length)
    (hBudget :
      (3 + 40 *
        (((kahanCoupledCoeffSteps fp v k hk).drop (i.val + 1)).length : ℝ)) *
          fp.u ≤ 1) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    |(kahanCoupledSourceCoeff steps i).s - 1| ≤
      2 * fp.u +
        2 * (3 + 40 * ((steps.drop (i.val + 1)).length : ℝ)) *
          fp.u ^ 2 := by
  dsimp
  let steps := kahanCoupledCoeffSteps fp v k hk
  let sourceRadius := fp.u + 3 * fp.u ^ 2
  have hu1 : fp.u ≤ 1 := by nlinarith
  have hmem : steps.get i ∈ steps := List.get_mem steps i
  have hS0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).s - 1| ≤
        sourceRadius := by
    have h :=
      kahanCoupledCoeffSteps_totalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_exactSub
        fp v k hk hu1 hExactSub (steps.get i) hmem
    have hle : fp.u + 2 * fp.u ^ 2 ≤ sourceRadius := by
      dsimp [sourceRadius]
      nlinarith [sq_nonneg fp.u]
    exact
      (by
        simpa [steps, sourceRadius, KahanState.totalCorrection,
          KahanCoupledCoeffStep.sourceCoeff,
          KahanCoupledCoeffStep.totalInputCoeff] using h.trans hle)
  have hE0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).e| ≤
        sourceRadius := by
    have h :=
      kahanCoupledCoeffSteps_D_abs_le_u_plus_three_u_sq_of_exactSub
        fp v k hk hu1 hExactSub (steps.get i) hmem
    simpa [steps, sourceRadius, KahanState.totalCorrection,
      KahanCoupledCoeffStep.sourceCoeff] using h
  have hsourceRadius_nonneg : 0 ≤ sourceRadius := by
    dsimp [sourceRadius]
    nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  have hTotal :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).s - 1| ≤
          |state.s - 1| * (1 + fp.u ^ 2) + fp.u ^ 2 +
            |state.e| * (fp.u + fp.u ^ 2) := by
    intro step hstep state
    simpa [steps] using
      kahanCoupledCoeffSteps_propagateTotalCorrection_totalDev_abs_le_of_exactSub
        fp v k hk hu1 hExactSub step hstep state
  have hCorrection :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).e| ≤
          (|state.s - 1| + 1) * (fp.u + fp.u ^ 2) +
            |state.e| * (2 * fp.u ^ 2) := by
    intro step hstep state
    simpa [steps] using
      kahanCoupledCoeffSteps_propagateTotalCorrection_correction_abs_le_of_exactSub
        fp v k hk hu1 hExactSub step hstep state
  exact
    kahanCoupledSourceCoeff_s_abs_sub_one_le_exactSubMajorant
      (u := fp.u) (A := 3) (S := sourceRadius) (E := sourceRadius)
      fp.u_nonneg huSmall (by norm_num) steps i
      (by simpa [steps] using hBudget)
      hS0 hE0 hsourceRadius_nonneg hsourceRadius_nonneg
      (by rfl) (by rfl) hTotal hCorrection

/-- A prefix-indexed family of explicit Kahan roundoff witnesses for the first
`k` Kahan steps.  This avoids depending on the arbitrary witness selected by
`Classical.choice`, which is essential for the exact-subtraction route. -/
def KahanPrefixDeltaWitnessFamily
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : Type :=
  (i : Fin k) →
    let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    KahanStepDeltaWitness fp (v idx)
      (kahanPrefixState fp v idx.val (Nat.le_of_lt idx.isLt))

/-- Prefix-level exactness surface for Algorithm 4.2's displayed correction
subtraction `temp - s`.  This is an operation-level bridge: it states the
subtraction is exact in the actual prefix trace, without committing to a
particular roundoff witness selected by `Classical.choice`. -/
def KahanPrefixCorrectionSubExact
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : Prop :=
  ∀ i : Fin k,
    let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    fp.fl_sub (kahanTrace fp v idx).temp (kahanTrace fp v idx).s =
      (kahanTrace fp v idx).temp - (kahanTrace fp v idx).s

/-- Construct an explicit prefix witness family from exact correction
subtraction in every processed Kahan prefix step. -/
noncomputable def kahanPrefixDeltaWitnessFamilyOfExactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hExactSubTrace : KahanPrefixCorrectionSubExact fp v k hk) :
    KahanPrefixDeltaWitnessFamily fp v k hk :=
  fun i =>
    let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    let hsubExact :
        fp.fl_sub
            (kahanStepTrace fp (v idx)
              (kahanPrefixState fp v idx.val (Nat.le_of_lt idx.isLt))).temp
            (kahanStepTrace fp (v idx)
              (kahanPrefixState fp v idx.val (Nat.le_of_lt idx.isLt))).s =
          (kahanStepTrace fp (v idx)
              (kahanPrefixState fp v idx.val (Nat.le_of_lt idx.isLt))).temp -
            (kahanStepTrace fp (v idx)
              (kahanPrefixState fp v idx.val (Nat.le_of_lt idx.isLt))).s := by
      have h := hExactSubTrace i
      simpa [KahanPrefixCorrectionSubExact, kahanTrace, idx] using h
    kahanStepTrace_deltaWitnessOfExactSub fp (v idx)
      (kahanPrefixState fp v idx.val (Nat.le_of_lt idx.isLt))
      hsubExact

/-- Coupled coefficient steps built from an explicit prefix witness family. -/
def kahanCoupledCoeffStepsOfWitnesses
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) :
    List KahanCoupledCoeffStep :=
  List.ofFn fun i : Fin k =>
    let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    kahanCoupledCoeffStepOfWitness fp v idx (W i)

/-- Prefix-indexed form of the general correction-residual cancellation for
an explicit witness family. -/
theorem kahanCoupledCoeffStepsOfWitnesses_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) :
    ∀ i : Fin k,
      let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
      |(kahanCoupledCoeffStepOfWitness fp v idx (W i)).correctionResidualCoeff +
          (W i).deltaSub| ≤
        7 * fp.u ^ 2 := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfWitness_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq
      fp v idx (W i) hu1

/-- Prefix-indexed form of
`residualCoeff - correctionResidualCoeff = deltaY + O(u^2)` for an explicit
witness family. -/
theorem kahanCoupledCoeffStepsOfWitnesses_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) :
    ∀ i : Fin k,
      let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
      |(kahanCoupledCoeffStepOfWitness fp v idx (W i)).residualCoeff -
          (kahanCoupledCoeffStepOfWitness fp v idx (W i)).correctionResidualCoeff -
          (W i).deltaY| ≤
        fp.u ^ 2 := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfWitness_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq
      fp v idx (W i)

/-- Prefix-indexed combined residual cancellation for an explicit witness
family. -/
theorem kahanCoupledCoeffStepsOfWitnesses_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) :
    ∀ i : Fin k,
      let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
      |(kahanCoupledCoeffStepOfWitness fp v idx (W i)).residualCoeff +
          (W i).deltaSub - (W i).deltaY| ≤
        8 * fp.u ^ 2 := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfWitness_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq
      fp v idx (W i) hu1

/-- Prefix-level exact-subtraction hypothesis for an explicit witness family. -/
def kahanCoupledCoeffStepsOfWitnessesExactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) : Prop :=
  ∀ i : Fin k, (W i).deltaSub = 0

/-- The witness family constructed from exact correction subtraction satisfies
the exact-subtraction predicate used by the coefficient theorem. -/
theorem kahanPrefixDeltaWitnessFamilyOfExactSub_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hExactSubTrace : KahanPrefixCorrectionSubExact fp v k hk) :
    kahanCoupledCoeffStepsOfWitnessesExactSub fp v k hk
      (kahanPrefixDeltaWitnessFamilyOfExactSub
        fp v k hk hExactSubTrace) := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  let hsubExact :
      fp.fl_sub
          (kahanStepTrace fp (v idx)
            (kahanPrefixState fp v idx.val (Nat.le_of_lt idx.isLt))).temp
          (kahanStepTrace fp (v idx)
            (kahanPrefixState fp v idx.val (Nat.le_of_lt idx.isLt))).s =
        (kahanStepTrace fp (v idx)
            (kahanPrefixState fp v idx.val (Nat.le_of_lt idx.isLt))).temp -
          (kahanStepTrace fp (v idx)
            (kahanPrefixState fp v idx.val (Nat.le_of_lt idx.isLt))).s := by
    have h := hExactSubTrace i
    simpa [KahanPrefixCorrectionSubExact, kahanTrace, idx] using h
  simpa [kahanPrefixDeltaWitnessFamilyOfExactSub, idx, hsubExact] using
    kahanStepTrace_deltaWitnessOfExactSub_deltaSub fp (v idx)
      (kahanPrefixState fp v idx.val (Nat.le_of_lt idx.isLt))
      hsubExact

/-- Exact-subtraction list-level old-total coefficient bound for explicit
witness-family Kahan steps. -/
theorem kahanCoupledCoeffStepsOfWitnesses_totalStateCoeff_abs_sub_one_le_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk)
    (hExactSub : kahanCoupledCoeffStepsOfWitnessesExactSub fp v k hk W) :
    ∀ step ∈ kahanCoupledCoeffStepsOfWitnesses fp v k hk W,
      |step.totalStateCoeff - 1| ≤ fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffStepsOfWitnesses, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfWitness_totalStateCoeff_abs_sub_one_le_u_sq_of_deltaSub_zero
      fp v idx (W i) (hExactSub i)

/-- Exact-subtraction list-level current-input total coefficient bound for
explicit witness-family Kahan steps. -/
theorem kahanCoupledCoeffStepsOfWitnesses_totalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk)
    (hExactSub : kahanCoupledCoeffStepsOfWitnessesExactSub fp v k hk W) :
    ∀ step ∈ kahanCoupledCoeffStepsOfWitnesses fp v k hk W,
      |step.totalInputCoeff - 1| ≤ fp.u + 2 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffStepsOfWitnesses, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfWitness_totalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_deltaSub_zero
      fp v idx (W i) hu1 (hExactSub i)

/-- Exact-subtraction list-level retained-correction residual bound for
explicit witness-family Kahan steps. -/
theorem kahanCoupledCoeffStepsOfWitnesses_residualCoeff_abs_le_u_plus_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk)
    (hExactSub : kahanCoupledCoeffStepsOfWitnessesExactSub fp v k hk W) :
    ∀ step ∈ kahanCoupledCoeffStepsOfWitnesses fp v k hk W,
      |step.residualCoeff| ≤ fp.u + fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffStepsOfWitnesses, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfWitness_residualCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero
      fp v idx (W i) hu1 (hExactSub i)

/-- Exact-subtraction list-level correction old-total coefficient bound for
explicit witness-family Kahan steps. -/
theorem kahanCoupledCoeffStepsOfWitnesses_C_abs_le_u_plus_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk)
    (hExactSub : kahanCoupledCoeffStepsOfWitnessesExactSub fp v k hk W) :
    ∀ step ∈ kahanCoupledCoeffStepsOfWitnesses fp v k hk W,
      |step.C| ≤ fp.u + fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffStepsOfWitnesses, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfWitness_C_abs_le_u_plus_u_sq_of_deltaSub_zero
      fp v idx (W i) (hExactSub i)

/-- Exact-subtraction list-level correction current-input coefficient bound
for explicit witness-family Kahan steps. -/
theorem kahanCoupledCoeffStepsOfWitnesses_D_abs_le_u_plus_three_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk)
    (hExactSub : kahanCoupledCoeffStepsOfWitnessesExactSub fp v k hk W) :
    ∀ step ∈ kahanCoupledCoeffStepsOfWitnesses fp v k hk W,
      |step.D| ≤ fp.u + 3 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffStepsOfWitnesses, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfWitness_D_abs_le_u_plus_three_u_sq_of_deltaSub_zero
      fp v idx (W i) hu1 (hExactSub i)

/-- Exact-subtraction list-level paired correction residual bound for explicit
witness-family Kahan steps. -/
theorem kahanCoupledCoeffStepsOfWitnesses_correctionResidualCoeff_abs_le_two_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk)
    (hExactSub : kahanCoupledCoeffStepsOfWitnessesExactSub fp v k hk W) :
    ∀ step ∈ kahanCoupledCoeffStepsOfWitnesses fp v k hk W,
      |step.correctionResidualCoeff| ≤ 2 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffStepsOfWitnesses, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfWitness_correctionResidualCoeff_abs_le_two_u_sq_of_deltaSub_zero
      fp v idx (W i) hu1 (hExactSub i)

/-- Exact-subtraction one-step propagation inequality for explicit
witness-family Kahan steps in paired-total coordinates. -/
theorem kahanCoupledCoeffStepsOfWitnesses_propagateTotalCorrection_totalDev_abs_le_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk)
    (hExactSub : kahanCoupledCoeffStepsOfWitnessesExactSub fp v k hk W) :
    ∀ step ∈ kahanCoupledCoeffStepsOfWitnesses fp v k hk W,
      ∀ state : KahanState,
        |(step.propagateTotalCorrection state).s - 1| ≤
          |state.s - 1| * (1 + fp.u ^ 2) + fp.u ^ 2 +
            |state.e| * (fp.u + fp.u ^ 2) := by
  intro step hmem state
  exact
    KahanCoupledCoeffStep.propagateTotalCorrection_totalDev_abs_le_of_bounds
      step state
      (kahanCoupledCoeffStepsOfWitnesses_totalStateCoeff_abs_sub_one_le_u_sq_of_exactSub
        fp v k hk W hExactSub step hmem)
      (kahanCoupledCoeffStepsOfWitnesses_residualCoeff_abs_le_u_plus_u_sq_of_exactSub
        fp v k hk hu1 W hExactSub step hmem)

/-- Exact-subtraction one-step correction propagation inequality for explicit
witness-family Kahan steps in paired-total coordinates. -/
theorem kahanCoupledCoeffStepsOfWitnesses_propagateTotalCorrection_correction_abs_le_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk)
    (hExactSub : kahanCoupledCoeffStepsOfWitnessesExactSub fp v k hk W) :
    ∀ step ∈ kahanCoupledCoeffStepsOfWitnesses fp v k hk W,
      ∀ state : KahanState,
        |(step.propagateTotalCorrection state).e| ≤
          (|state.s - 1| + 1) * (fp.u + fp.u ^ 2) +
            |state.e| * (2 * fp.u ^ 2) := by
  intro step hmem state
  exact
    KahanCoupledCoeffStep.propagateTotalCorrection_correction_abs_le_of_bounds
      step state
      (kahanCoupledCoeffStepsOfWitnesses_C_abs_le_u_plus_u_sq_of_exactSub
        fp v k hk W hExactSub step hmem)
      (kahanCoupledCoeffStepsOfWitnesses_correctionResidualCoeff_abs_le_two_u_sq_of_exactSub
        fp v k hk hu1 W hExactSub step hmem)

/-- Source-coefficient collapse for the returned Kahan sum along an explicit
exact-subtraction witness-family route. -/
theorem kahanCoupledCoeffStepsOfWitnesses_sourceCoeff_s_abs_sub_one_le_two_u_plus_exactSubMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk)
    (huSmall : fp.u ≤ 1 / 64)
    (hExactSub : kahanCoupledCoeffStepsOfWitnessesExactSub fp v k hk W)
    (i : Fin (kahanCoupledCoeffStepsOfWitnesses fp v k hk W).length)
    (hBudget :
      (3 + 40 *
        (((kahanCoupledCoeffStepsOfWitnesses fp v k hk W).drop
          (i.val + 1)).length : ℝ)) * fp.u ≤ 1) :
    let steps := kahanCoupledCoeffStepsOfWitnesses fp v k hk W
    |(kahanCoupledSourceCoeff steps i).s - 1| ≤
      2 * fp.u +
        2 * (3 + 40 * ((steps.drop (i.val + 1)).length : ℝ)) *
          fp.u ^ 2 := by
  dsimp
  let steps := kahanCoupledCoeffStepsOfWitnesses fp v k hk W
  let sourceRadius := fp.u + 3 * fp.u ^ 2
  have hu1 : fp.u ≤ 1 := by nlinarith
  have hmem : steps.get i ∈ steps := List.get_mem steps i
  have hS0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).s - 1| ≤
        sourceRadius := by
    have h :=
      kahanCoupledCoeffStepsOfWitnesses_totalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_exactSub
        fp v k hk hu1 W hExactSub (steps.get i) hmem
    have hle : fp.u + 2 * fp.u ^ 2 ≤ sourceRadius := by
      dsimp [sourceRadius]
      nlinarith [sq_nonneg fp.u]
    exact
      (by
        simpa [steps, sourceRadius, KahanState.totalCorrection,
          KahanCoupledCoeffStep.sourceCoeff,
          KahanCoupledCoeffStep.totalInputCoeff] using h.trans hle)
  have hE0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).e| ≤
        sourceRadius := by
    have h :=
      kahanCoupledCoeffStepsOfWitnesses_D_abs_le_u_plus_three_u_sq_of_exactSub
        fp v k hk hu1 W hExactSub (steps.get i) hmem
    simpa [steps, sourceRadius, KahanState.totalCorrection,
      KahanCoupledCoeffStep.sourceCoeff] using h
  have hsourceRadius_nonneg : 0 ≤ sourceRadius := by
    dsimp [sourceRadius]
    nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  have hTotal :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).s - 1| ≤
          |state.s - 1| * (1 + fp.u ^ 2) + fp.u ^ 2 +
            |state.e| * (fp.u + fp.u ^ 2) := by
    intro step hstep state
    simpa [steps] using
      kahanCoupledCoeffStepsOfWitnesses_propagateTotalCorrection_totalDev_abs_le_of_exactSub
        fp v k hk hu1 W hExactSub step hstep state
  have hCorrection :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).e| ≤
          (|state.s - 1| + 1) * (fp.u + fp.u ^ 2) +
            |state.e| * (2 * fp.u ^ 2) := by
    intro step hstep state
    simpa [steps] using
      kahanCoupledCoeffStepsOfWitnesses_propagateTotalCorrection_correction_abs_le_of_exactSub
        fp v k hk hu1 W hExactSub step hstep state
  exact
    kahanCoupledSourceCoeff_s_abs_sub_one_le_exactSubMajorant
      (u := fp.u) (A := 3) (S := sourceRadius) (E := sourceRadius)
      fp.u_nonneg huSmall (by norm_num) steps i
      (by simpa [steps] using hBudget)
      hS0 hE0 hsourceRadius_nonneg hsourceRadius_nonneg
      (by rfl) (by rfl) hTotal hCorrection

/-- Source-shaped collapse of the paired majorant for the compensated-total
coefficient of each propagated Kahan source vector.  This closes the
majorant-collapse dependency for the `s+e` coefficient; the final returned
stored-sum coefficient still needs the remaining paired-cancellation step. -/
theorem kahanCoupledCoeffSteps_sourceTotalCoeff_abs_sub_one_le_two_u_plus_majorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (huSmall : fp.u ≤ 1 / 64)
    (i : Fin (kahanCoupledCoeffSteps fp v k hk).length)
    (hBudget :
      (9 + 200 *
        (((kahanCoupledCoeffSteps fp v k hk).drop (i.val + 1)).length : ℝ)) *
          fp.u ≤ 1) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    |kahanCoupledSourceTotalCoeff steps i - 1| ≤
      2 * fp.u +
        (9 + 200 * ((steps.drop (i.val + 1)).length : ℝ)) * fp.u ^ 2 := by
  dsimp
  let steps := kahanCoupledCoeffSteps fp v k hk
  let suffix := steps.drop (i.val + 1)
  have hu1 : fp.u ≤ 1 := by nlinarith
  have hpaired :=
    (kahanCoupledCoeffSteps_sourceTotalCorrectionCoeff_abs_le_pairedCoeffMajorant
      fp v k hk hu1 i).1
  have hsigma_nonneg : 0 ≤ fp.u * (1 + fp.u) ^ 2 := by
    exact mul_nonneg fp.u_nonneg (sq_nonneg (1 + fp.u))
  have hsigma_le : fp.u * (1 + fp.u) ^ 2 ≤ 4 * fp.u := by
    have h1u : 1 + fp.u ≤ 2 := by nlinarith
    have h1u_nonneg : 0 ≤ 1 + fp.u := by nlinarith [fp.u_nonneg]
    have hsquare : (1 + fp.u) ^ 2 ≤ 4 := by
      have hmul := mul_le_mul h1u h1u h1u_nonneg (by norm_num)
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsquare fp.u_nonneg
    nlinarith
  have hsourceCorrection :
      fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) ≤ 12 * fp.u := by
    have h2u : 2 + fp.u ≤ 3 := by nlinarith
    have h2u_nonneg : 0 ≤ 2 + fp.u := by nlinarith [fp.u_nonneg]
    have h12_nonneg : 0 ≤ 4 * fp.u := by nlinarith [fp.u_nonneg]
    have hmul := mul_le_mul hsigma_le h2u h2u_nonneg h12_nonneg
    nlinarith
  have hcollapse :=
    kahanCoupledPairedCoeffMajorant_kahanConstants_le_two_u_plus
      (u := fp.u) (A := 9)
      (S := 2 * fp.u + 9 * fp.u ^ 2)
      (E := fp.u * (1 + fp.u) ^ 2 * (2 + fp.u))
      fp.u_nonneg huSmall (by norm_num) suffix
      (by simpa [steps, suffix] using hBudget)
      (by rfl) hsourceCorrection
  calc
    |kahanCoupledSourceTotalCoeff steps i - 1|
        = |(kahanCoupledSourceTotalCorrectionCoeff steps i).s - 1| := by
          rfl
    _ ≤
        (kahanCoupledPairedCoeffMajorant (3 * fp.u ^ 2)
          (2 * fp.u + 12 * fp.u ^ 2)
          (fp.u * (1 + fp.u) ^ 2)
          (fp.u * (1 + fp.u) ^ 2 * (3 + fp.u))
          suffix
          (2 * fp.u + 9 * fp.u ^ 2)
          (fp.u * (1 + fp.u) ^ 2 * (2 + fp.u))).s := by
        simpa [steps, suffix] using hpaired
    _ ≤ 2 * fp.u + (9 + 200 * (suffix.length : ℝ)) * fp.u ^ 2 :=
        hcollapse.1
    _ = 2 * fp.u +
        (9 + 200 * ((steps.drop (i.val + 1)).length : ℝ)) * fp.u ^ 2 := by
        simp [suffix]

/-- The list fold over coupled Kahan coefficient steps is the matching
`Fin.foldl` prefix recurrence. -/
theorem kahanCoupledCoeffSteps_fold_eq_finFold
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (init : KahanState) :
    kahanCoupledCoeffFold (kahanCoupledCoeffSteps fp v k hk) init =
      Fin.foldl k
        (fun state i =>
          let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
          let step := kahanCoupledCoeffStepOfIndex fp v idx
          step.next state)
        init := by
  dsimp [kahanCoupledCoeffFold, kahanCoupledCoeffSteps]
  rw [list_foldl_ofFn_eq_fin_foldl]

/-- The coupled coefficient recurrence over the first `k` actual Kahan
prefix-trace steps produces the full stored-sum/correction prefix state. -/
theorem kahanCoupledCoeffSteps_finFold_eq_prefix_state
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      Fin.foldl k
        (fun state i =>
          let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
          let step := kahanCoupledCoeffStepOfIndex fp v idx
          step.next state)
        KahanState.zero =
      kahanPrefixState fp v k hk
  | 0, _hk => by
      simp [kahanPrefixState, KahanState.zero]
  | k + 1, hk => by
      have hprev_le : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let idx : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let prev := kahanPrefixState fp v k hprev_le
      let step := kahanCoupledCoeffStepOfIndex fp v idx
      have hih :=
        kahanCoupledCoeffSteps_finFold_eq_prefix_state fp v k hprev_le
      have hih' :
          Fin.foldl k
            (fun state i =>
              let idx : Fin n := ⟨(i.castSucc).val,
                Nat.lt_of_lt_of_le (i.castSucc).isLt hk⟩
              let step := kahanCoupledCoeffStepOfIndex fp v idx
              step.next state)
            KahanState.zero = prev := by
        simpa [prev] using hih
      have hfoldPrefix :
          kahanPrefixState fp v (k + 1) hk =
            kahanStep fp (v idx) prev := by
        unfold kahanPrefixState
        rw [Fin.foldl_succ_last]
        rfl
      have hstep :
          kahanStep fp (v idx) prev = step.next prev := by
        have htrace := kahanTrace_eq_coupledCoeffStep_next fp v idx
        dsimp at htrace
        simpa [idx, prev, step, kahanTrace, kahanStep,
          KahanStepTrace.nextState] using htrace
      rw [Fin.foldl_succ_last]
      rw [hih']
      rw [hfoldPrefix, hstep]
      rfl

/-- The list of coupled coefficient steps for the first `k` actual Kahan
steps folds from zero to the full stored-sum/correction prefix state. -/
theorem kahanCoupledCoeffSteps_fold_zero_eq_prefix_state
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    kahanCoupledCoeffFold
        (kahanCoupledCoeffSteps fp v k hk) KahanState.zero =
      kahanPrefixState fp v k hk := by
  rw [kahanCoupledCoeffSteps_fold_eq_finFold]
  exact kahanCoupledCoeffSteps_finFold_eq_prefix_state fp v k hk

/-- The propagated source-vector unroll of the first `k` concrete coupled
Kahan steps is exactly the actual prefix `(s,e)` state. -/
theorem kahanCoupledCoeffSteps_sourceUnroll_eq_prefix_state
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    kahanCoupledSourceUnroll (kahanCoupledCoeffSteps fp v k hk) =
      kahanPrefixState fp v k hk := by
  rw [← kahanCoupledCoeffFold_zero_eq_sourceUnroll]
  exact kahanCoupledCoeffSteps_fold_zero_eq_prefix_state fp v k hk

/-- Returned stored sum of the first `k` concrete Kahan coupled steps as an
explicit source-input coefficient sum. -/
theorem kahanCoupledCoeffSteps_prefixState_s_eq_sum_sourceCoeff
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    (kahanPrefixState fp v k hk).s =
      ∑ i : Fin steps.length,
        (steps.get i).x * (kahanCoupledSourceCoeff steps i).s := by
  dsimp
  rw [← kahanCoupledCoeffSteps_sourceUnroll_eq_prefix_state fp v k hk]
  exact kahanCoupledSourceUnroll_s_eq_sum_sourceCoeff
    (kahanCoupledCoeffSteps fp v k hk)

/-- Retained correction of the first `k` concrete Kahan coupled steps as an
explicit source-input coefficient sum. -/
theorem kahanCoupledCoeffSteps_prefixState_e_eq_sum_sourceCoeff
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    (kahanPrefixState fp v k hk).e =
      ∑ i : Fin steps.length,
        (steps.get i).x * (kahanCoupledSourceCoeff steps i).e := by
  dsimp
  rw [← kahanCoupledCoeffSteps_sourceUnroll_eq_prefix_state fp v k hk]
  exact kahanCoupledSourceUnroll_e_eq_sum_sourceCoeff
    (kahanCoupledCoeffSteps fp v k hk)

/-- Compensated total of the first `k` concrete Kahan coupled steps as an
explicit source-input sum over the paired source coefficients. -/
theorem kahanCoupledCoeffSteps_prefixState_total_eq_sum_sourceTotalCoeff
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    (kahanPrefixState fp v k hk).s +
        (kahanPrefixState fp v k hk).e =
      ∑ i : Fin steps.length,
        (steps.get i).x * kahanCoupledSourceTotalCoeff steps i := by
  dsimp
  rw [← kahanCoupledCoeffSteps_sourceUnroll_eq_prefix_state fp v k hk]
  exact kahanCoupledSourceUnroll_total_eq_sum_sourceTotalCoeff
    (kahanCoupledCoeffSteps fp v k hk)

/-- The list fold over explicit-witness coupled Kahan coefficient steps is the
matching `Fin.foldl` prefix recurrence. -/
theorem kahanCoupledCoeffStepsOfWitnesses_fold_eq_finFold
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) (init : KahanState) :
    kahanCoupledCoeffFold
        (kahanCoupledCoeffStepsOfWitnesses fp v k hk W) init =
      Fin.foldl k
        (fun state i =>
          let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
          let step := kahanCoupledCoeffStepOfWitness fp v idx (W i)
          step.next state)
        init := by
  dsimp [kahanCoupledCoeffFold, kahanCoupledCoeffStepsOfWitnesses]
  rw [list_foldl_ofFn_eq_fin_foldl]

/-- The explicit-witness coupled coefficient recurrence over the first `k`
Kahan prefix-trace steps produces the actual stored-sum/correction prefix
state. -/
theorem kahanCoupledCoeffStepsOfWitnesses_finFold_eq_prefix_state
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n)
      (W : KahanPrefixDeltaWitnessFamily fp v k hk),
      Fin.foldl k
        (fun state i =>
          let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
          let step := kahanCoupledCoeffStepOfWitness fp v idx (W i)
          step.next state)
        KahanState.zero =
      kahanPrefixState fp v k hk
  | 0, _hk, _W => by
      simp [kahanPrefixState, KahanState.zero]
  | k + 1, hk, W => by
      have hprev_le : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let last : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
      let idx : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let Wprev : KahanPrefixDeltaWitnessFamily fp v k hprev_le :=
        fun i => by
          simpa using W i.castSucc
      let prev := kahanPrefixState fp v k hprev_le
      let step := kahanCoupledCoeffStepOfWitness fp v idx (W last)
      have hih :=
        kahanCoupledCoeffStepsOfWitnesses_finFold_eq_prefix_state
          fp v k hprev_le Wprev
      have hih' :
          Fin.foldl k
            (fun state i =>
              let idx : Fin n := ⟨(i.castSucc).val,
                Nat.lt_of_lt_of_le (i.castSucc).isLt hk⟩
              let step := kahanCoupledCoeffStepOfWitness fp v idx
                (W i.castSucc)
              step.next state)
            KahanState.zero = prev := by
        simpa [Wprev, prev] using hih
      have hfoldPrefix :
          kahanPrefixState fp v (k + 1) hk =
            kahanStep fp (v idx) prev := by
        unfold kahanPrefixState
        rw [Fin.foldl_succ_last]
        rfl
      have hstep :
          kahanStep fp (v idx) prev = step.next prev := by
        have htrace :=
          kahanTrace_eq_coupledCoeffStepOfWitness_next fp v idx (W last)
        dsimp at htrace
        simpa [idx, last, prev, step, kahanTrace, kahanStep,
          KahanStepTrace.nextState] using htrace
      rw [Fin.foldl_succ_last]
      rw [hih']
      rw [hfoldPrefix, hstep]
      rfl

/-- Explicit-witness coupled Kahan steps fold from zero to the actual prefix
state. -/
theorem kahanCoupledCoeffStepsOfWitnesses_fold_zero_eq_prefix_state
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) :
    kahanCoupledCoeffFold
        (kahanCoupledCoeffStepsOfWitnesses fp v k hk W) KahanState.zero =
      kahanPrefixState fp v k hk := by
  rw [kahanCoupledCoeffStepsOfWitnesses_fold_eq_finFold]
  exact kahanCoupledCoeffStepsOfWitnesses_finFold_eq_prefix_state
    fp v k hk W

/-- The propagated source-vector unroll of explicit-witness coupled Kahan
steps is exactly the actual prefix `(s,e)` state. -/
theorem kahanCoupledCoeffStepsOfWitnesses_sourceUnroll_eq_prefix_state
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) :
    kahanCoupledSourceUnroll
        (kahanCoupledCoeffStepsOfWitnesses fp v k hk W) =
      kahanPrefixState fp v k hk := by
  rw [← kahanCoupledCoeffFold_zero_eq_sourceUnroll]
  exact kahanCoupledCoeffStepsOfWitnesses_fold_zero_eq_prefix_state
    fp v k hk W

/-- Returned stored sum of the first `k` explicit-witness coupled Kahan steps
as an explicit source-input coefficient sum. -/
theorem kahanCoupledCoeffStepsOfWitnesses_prefixState_s_eq_sum_sourceCoeff
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) :
    let steps := kahanCoupledCoeffStepsOfWitnesses fp v k hk W
    (kahanPrefixState fp v k hk).s =
      ∑ i : Fin steps.length,
        (steps.get i).x * (kahanCoupledSourceCoeff steps i).s := by
  dsimp
  rw [← kahanCoupledCoeffStepsOfWitnesses_sourceUnroll_eq_prefix_state
    fp v k hk W]
  exact kahanCoupledSourceUnroll_s_eq_sum_sourceCoeff
    (kahanCoupledCoeffStepsOfWitnesses fp v k hk W)

/-- Retained correction of the first `k` explicit-witness coupled Kahan steps
as an explicit source-input coefficient sum. -/
theorem kahanCoupledCoeffStepsOfWitnesses_prefixState_e_eq_sum_sourceCoeff
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) :
    let steps := kahanCoupledCoeffStepsOfWitnesses fp v k hk W
    (kahanPrefixState fp v k hk).e =
      ∑ i : Fin steps.length,
        (steps.get i).x * (kahanCoupledSourceCoeff steps i).e := by
  dsimp
  rw [← kahanCoupledCoeffStepsOfWitnesses_sourceUnroll_eq_prefix_state
    fp v k hk W]
  exact kahanCoupledSourceUnroll_e_eq_sum_sourceCoeff
    (kahanCoupledCoeffStepsOfWitnesses fp v k hk W)

/-- Compensated total of the first `k` explicit-witness coupled Kahan steps as
an explicit source-input sum over paired source coefficients. -/
theorem kahanCoupledCoeffStepsOfWitnesses_prefixState_total_eq_sum_sourceTotalCoeff
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) :
    let steps := kahanCoupledCoeffStepsOfWitnesses fp v k hk W
    (kahanPrefixState fp v k hk).s +
        (kahanPrefixState fp v k hk).e =
      ∑ i : Fin steps.length,
        (steps.get i).x * kahanCoupledSourceTotalCoeff steps i := by
  dsimp
  rw [← kahanCoupledCoeffStepsOfWitnesses_sourceUnroll_eq_prefix_state
    fp v k hk W]
  exact kahanCoupledSourceUnroll_total_eq_sum_sourceTotalCoeff
    (kahanCoupledCoeffStepsOfWitnesses fp v k hk W)

/-- The residual-aware affine coefficient step induced by one indexed Kahan
prefix-trace step. -/
noncomputable def kahanAffineCoeffStepOfIndex
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    KahanAffineCoeffStep :=
  let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
  let w := kahanTrace_deltaWitness fp v i
  { A := kahanTotalStateCoeff w.deltaS w.deltaSub w.deltaE
    B := kahanTotalInputCoeff w.deltaY w.deltaS w.deltaSub w.deltaE
    R := kahanTotalResidualCoeff w.deltaY w.deltaS w.deltaSub w.deltaE
    x := v i
    e := state.e }

/-- One indexed Kahan prefix-trace step satisfies the residual-aware affine
coefficient recurrence. -/
theorem kahanTrace_total_eq_affineCoeffStep
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    let step := kahanAffineCoeffStepOfIndex fp v i
    (kahanTrace fp v i).s + (kahanTrace fp v i).e =
      step.A * (state.s + state.e) + step.source := by
  dsimp
  have h := kahanTrace_deltaWitness_total_compensated_total_coefficients fp v i
  dsimp at h
  rw [h]
  dsimp [kahanAffineCoeffStepOfIndex, KahanAffineCoeffStep.source]
  ring

/-- The old-total coefficient of the actual indexed Kahan affine step is
bounded by `1 + 3*u^2` under the local small-`u` hypothesis. -/
theorem kahanAffineCoeffStepOfIndex_A_abs_le_one_plus_three_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    |(kahanAffineCoeffStepOfIndex fp v i).A| ≤
      1 + 3 * fp.u ^ 2 := by
  let A := (kahanAffineCoeffStepOfIndex fp v i).A
  have hA1 : |A - 1| ≤ 3 * fp.u ^ 2 := by
    simpa [A, kahanAffineCoeffStepOfIndex] using
      kahanTotalStateCoeff_abs_sub_one_le_three_u_sq
        (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
        (deltaSub := (kahanTrace_deltaWitness fp v i).deltaSub)
        (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
        (u := fp.u) fp.u_nonneg hu1
        (kahanTrace_deltaWitness fp v i).h_deltaS
        (kahanTrace_deltaWitness fp v i).h_deltaSub
        (kahanTrace_deltaWitness fp v i).h_deltaE
  have hrewrite : A = (A - 1) + 1 := by ring
  calc
    |A| = |(A - 1) + 1| := congrArg abs hrewrite
    _ ≤ |A - 1| + |(1 : ℝ)| := abs_add_le (A - 1) 1
    _ ≤ 3 * fp.u ^ 2 + 1 := by
          exact add_le_add hA1 (by norm_num)
    _ = 1 + 3 * fp.u ^ 2 := by ring

/-- The old-total coefficient of the actual indexed Kahan affine step differs
from one by at most `3*u^2`. -/
theorem kahanAffineCoeffStepOfIndex_A_abs_sub_one_le_three_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    |(kahanAffineCoeffStepOfIndex fp v i).A - 1| ≤
      3 * fp.u ^ 2 := by
  simpa [kahanAffineCoeffStepOfIndex] using
    kahanTotalStateCoeff_abs_sub_one_le_three_u_sq
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaSub := (kahanTrace_deltaWitness fp v i).deltaSub)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaSub
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- The current-input coefficient of the actual indexed Kahan affine step
differs from one by at most `2*u + 9*u^2`. -/
theorem kahanAffineCoeffStepOfIndex_B_abs_sub_one_le_two_u_plus_nine_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    |(kahanAffineCoeffStepOfIndex fp v i).B - 1| ≤
      2 * fp.u + 9 * fp.u ^ 2 := by
  simpa [kahanAffineCoeffStepOfIndex] using
    kahanTotalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaSub := (kahanTrace_deltaWitness fp v i).deltaSub)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaSub
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- The retained-correction coefficient of the actual indexed Kahan affine
step satisfies the local small-`u` residual-coefficient bound. -/
theorem kahanAffineCoeffStepOfIndex_R_abs_le_two_u_plus_twelve_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    |(kahanAffineCoeffStepOfIndex fp v i).R| ≤
      2 * fp.u + 12 * fp.u ^ 2 := by
  simpa [kahanAffineCoeffStepOfIndex] using
    kahanTotalResidualCoeff_abs_le_two_u_plus_twelve_u_sq
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaSub := (kahanTrace_deltaWitness fp v i).deltaSub)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaSub
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- The retained-correction source contribution of the actual indexed Kahan
affine step is controlled by the local residual-coefficient radius times the
retained correction. -/
theorem kahanAffineCoeffStepOfIndex_correctionSource_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    let step := kahanAffineCoeffStepOfIndex fp v i
    |step.correctionSource| ≤
      (2 * fp.u + 12 * fp.u ^ 2) * |step.e| := by
  dsimp
  have hR :=
    kahanAffineCoeffStepOfIndex_R_abs_le_two_u_plus_twelve_u_sq
      fp v i hu1
  calc
    |(kahanAffineCoeffStepOfIndex fp v i).correctionSource|
        = |(kahanAffineCoeffStepOfIndex fp v i).R| *
            |(kahanAffineCoeffStepOfIndex fp v i).e| := by
          rw [KahanAffineCoeffStep.correctionSource, abs_mul]
    _ ≤ (2 * fp.u + 12 * fp.u ^ 2) *
          |(kahanAffineCoeffStepOfIndex fp v i).e| := by
        exact mul_le_mul_of_nonneg_right hR (abs_nonneg _)

/-- The retained-correction source contribution of the actual indexed Kahan
affine step is controlled by the input-only retained-correction majorant for
that prefix.

This is the local handoff from the concrete residual coefficient bound to the
stored-sum-free majorants used by the remaining Goldberg/Knuth coefficient
recursion. -/
theorem kahanAffineCoeffStepOfIndex_correctionSource_abs_le_inputMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    let step := kahanAffineCoeffStepOfIndex fp v i
    |step.correctionSource| ≤
      (2 * fp.u + 12 * fp.u ^ 2) *
        (kahanInputAbsMajorant fp v i.val (Nat.le_of_lt i.isLt)).e := by
  dsimp
  have hsource :=
    kahanAffineCoeffStepOfIndex_correctionSource_abs_le fp v i hu1
  have he :=
    kahanPrefixState_e_abs_le_inputMajorant
      fp v i.val (Nat.le_of_lt i.isLt)
  have hcoef : 0 ≤ 2 * fp.u + 12 * fp.u ^ 2 := by
    nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  calc
    |(kahanAffineCoeffStepOfIndex fp v i).correctionSource|
        ≤ (2 * fp.u + 12 * fp.u ^ 2) *
            |(kahanAffineCoeffStepOfIndex fp v i).e| := by
          simpa [kahanAffineCoeffStepOfIndex] using hsource
    _ ≤ (2 * fp.u + 12 * fp.u ^ 2) *
            (kahanInputAbsMajorant fp v i.val (Nat.le_of_lt i.isLt)).e := by
          exact mul_le_mul_of_nonneg_left he hcoef

/-- The first `k` indexed Kahan prefix-trace steps as residual-aware affine
coefficient steps. -/
noncomputable def kahanAffineCoeffSteps
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    List KahanAffineCoeffStep :=
  List.ofFn (fun i : Fin k =>
    kahanAffineCoeffStepOfIndex fp v
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩)

/-- Every concrete affine coefficient step in the first `k` Kahan prefix steps
has old-total coefficient bounded by `1 + 3*u^2`. -/
theorem kahanAffineCoeffSteps_A_abs_le_one_plus_three_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) :
    ∀ step ∈ kahanAffineCoeffSteps fp v k hk,
      |step.A| ≤ 1 + 3 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanAffineCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanAffineCoeffStepOfIndex_A_abs_le_one_plus_three_u_sq
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ hu1

/-- Every concrete affine coefficient step in the first `k` Kahan prefix steps
has old-total coefficient within `3*u^2` of one. -/
theorem kahanAffineCoeffSteps_A_abs_sub_one_le_three_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) :
    ∀ step ∈ kahanAffineCoeffSteps fp v k hk,
      |step.A - 1| ≤ 3 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanAffineCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanAffineCoeffStepOfIndex_A_abs_sub_one_le_three_u_sq
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ hu1

/-- Every concrete affine coefficient step in the first `k` Kahan prefix steps
has current-input coefficient within `2*u + 9*u^2` of one. -/
theorem kahanAffineCoeffSteps_B_abs_sub_one_le_two_u_plus_nine_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) :
    ∀ step ∈ kahanAffineCoeffSteps fp v k hk,
      |step.B - 1| ≤ 2 * fp.u + 9 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanAffineCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanAffineCoeffStepOfIndex_B_abs_sub_one_le_two_u_plus_nine_u_sq
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ hu1

/-- The old-total coefficient product for the first `k` concrete Kahan prefix
steps is bounded by `(1 + 3*u^2)^k`. -/
theorem kahanAffineCoeffSteps_tailProd_abs_le_one_plus_three_u_sq_pow
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) :
    |kahanAffineCoeffTailProd (kahanAffineCoeffSteps fp v k hk)| ≤
      (1 + 3 * fp.u ^ 2) ^ k := by
  have hrho : 0 ≤ 1 + 3 * fp.u ^ 2 := by
    nlinarith [sq_nonneg fp.u]
  have hbound :=
    kahanAffineCoeffTailProd_abs_le_pow
      (rho := 1 + 3 * fp.u ^ 2) hrho
      (kahanAffineCoeffSteps fp v k hk)
      (kahanAffineCoeffSteps_A_abs_le_one_plus_three_u_sq
        fp v k hk hu1)
  simpa [kahanAffineCoeffSteps] using hbound

/-- Product-form radius for the current-input coefficient induced by a Kahan
affine coefficient unroll.

For input index `i`, the exponent is the number of later prefix steps whose
old-total coefficients multiply the local current-input coefficient. -/
def kahanAffineInputCoeffProductRadius
    (fp : FPModel) (steps : List KahanAffineCoeffStep)
    (i : Fin steps.length) : ℝ :=
  (1 + 3 * fp.u ^ 2) ^ (steps.drop (i.val + 1)).length *
      (2 * fp.u + 9 * fp.u ^ 2) +
    ((1 + 3 * fp.u ^ 2) ^ (steps.drop (i.val + 1)).length - 1)

/-- The product-form input coefficient in the first `k` concrete Kahan prefix
steps is bounded by the explicit product radius. -/
theorem kahanAffineCoeffSteps_inputCoeff_abs_le_productRadius
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (hu1 : fp.u ≤ 1)
    (i : Fin (kahanAffineCoeffSteps fp v k hk).length) :
    let steps := kahanAffineCoeffSteps fp v k hk
    |kahanAffineInputCoeff steps i| ≤
      kahanAffineInputCoeffProductRadius fp steps i := by
  dsimp
  let steps := kahanAffineCoeffSteps fp v k hk
  have hA : ∀ step ∈ steps, |step.A - 1| ≤ 3 * fp.u ^ 2 := by
    simpa [steps] using
      kahanAffineCoeffSteps_A_abs_sub_one_le_three_u_sq
        fp v k hk hu1
  have hB :
      ∀ step ∈ steps, |step.B - 1| ≤
        2 * fp.u + 9 * fp.u ^ 2 := by
    simpa [steps] using
      kahanAffineCoeffSteps_B_abs_sub_one_le_two_u_plus_nine_u_sq
        fp v k hk hu1
  simpa [steps, kahanAffineInputCoeffProductRadius] using
    kahanAffineInputCoeff_abs_le_productRadius
      (eta := 3 * fp.u ^ 2)
      (beta := 2 * fp.u + 9 * fp.u ^ 2)
      (by nlinarith [sq_nonneg fp.u]) steps hA hB i

/-- Concrete source-shaped collapse of the Kahan product-form input radius.

For `m` later affine steps, if the second-order product budget
`m * (3*u^2)` is at most `1/2`, then the product-form radius is bounded by
`2*u + (9 + 72*m)*u^2`.  This closes the product-radius half of the final
C4.5 `2*u + C*n*u^2` collapse. -/
theorem kahanAffineInputCoeffProductRadius_le_two_u_plus
    (fp : FPModel) (steps : List KahanAffineCoeffStep)
    (i : Fin steps.length) (hu1 : fp.u ≤ 1)
    (hsmall :
      ((steps.drop (i.val + 1)).length : ℝ) * (3 * fp.u ^ 2) ≤ 1 / 2) :
    kahanAffineInputCoeffProductRadius fp steps i ≤
      2 * fp.u +
        (9 + 72 * ((steps.drop (i.val + 1)).length : ℝ)) * fp.u ^ 2 := by
  let m : ℕ := (steps.drop (i.val + 1)).length
  let u : ℝ := fp.u
  let c : ℝ := 3 * u ^ 2
  let b : ℝ := 2 * u + 9 * u ^ 2
  have hu0 : 0 ≤ u := by
    simpa [u] using fp.u_nonneg
  have hc0 : 0 ≤ c := by
    dsimp [c]
    nlinarith [sq_nonneg u]
  have hgeom :
      (1 + c) ^ m - 1 ≤ 2 * ((m : ℝ) * c) := by
    exact one_add_pow_sub_one_le_two_mul_nat_mul_of_nat_mul_le_half
      m hc0 (by simpa [m, c, u] using hsmall)
  have hgeom' :
      (1 + c) ^ m - 1 ≤ 6 * (m : ℝ) * u ^ 2 := by
    calc
      (1 + c) ^ m - 1 ≤ 2 * ((m : ℝ) * c) := hgeom
      _ = 6 * (m : ℝ) * u ^ 2 := by
          simp [c]
          ring
  have hb1_nonneg : 0 ≤ b + 1 := by
    dsimp [b]
    nlinarith [hu0, sq_nonneg u]
  have hu_sq_le_one : u ^ 2 ≤ 1 := by
    have hmul :=
      mul_le_mul hu1 hu1 hu0 (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hb1_le : b + 1 ≤ 12 := by
    dsimp [b]
    nlinarith [hu0, hu1, hu_sq_le_one]
  have hD_nonneg : 0 ≤ 6 * (m : ℝ) * u ^ 2 := by
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
    nlinarith [hm0, sq_nonneg u]
  have hscaled :
      ((1 + c) ^ m - 1) * (b + 1) ≤
        (6 * (m : ℝ) * u ^ 2) * (b + 1) := by
    exact mul_le_mul_of_nonneg_right hgeom' hb1_nonneg
  have hscaled' :
      (6 * (m : ℝ) * u ^ 2) * (b + 1) ≤
        72 * (m : ℝ) * u ^ 2 := by
    calc
      (6 * (m : ℝ) * u ^ 2) * (b + 1)
          ≤ (6 * (m : ℝ) * u ^ 2) * 12 := by
              exact mul_le_mul_of_nonneg_left hb1_le hD_nonneg
      _ = 72 * (m : ℝ) * u ^ 2 := by ring
  calc
    kahanAffineInputCoeffProductRadius fp steps i =
        b + (((1 + c) ^ m - 1) * (b + 1)) := by
          simp [kahanAffineInputCoeffProductRadius, m, c, b, u]
          ring
    _ ≤ b + 72 * (m : ℝ) * u ^ 2 := by
        nlinarith [hscaled, hscaled']
    _ = 2 * fp.u +
        (9 + 72 * ((steps.drop (i.val + 1)).length : ℝ)) * fp.u ^ 2 := by
        simp [b, m, u]
        ring

/-- Propagated retained-correction source contribution for the first `k`
Kahan steps, bounded only by input magnitudes through the coupled prefix
majorants.

The right-hand side charges prefix `j` by the input-only correction majorant
after `j` earlier steps, the residual coefficient radius `2*u + 12*u^2`, and
the product radius `(1 + 3*u^2)` for each later old-total coefficient. -/
theorem kahanAffineCoeffSteps_correctionAbsUnroll_le_inputMajorantBudget
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (hu1 : fp.u ≤ 1) :
    kahanAffineCorrectionAbsUnroll (kahanAffineCoeffSteps fp v k hk) ≤
      kahanAffineCorrectionIndexedBudget
        (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
        (fun j =>
          if hj : j < k then
            (kahanInputAbsMajorant fp v j
              (Nat.le_trans (Nat.le_of_lt hj) hk)).e
          else 0)
        (kahanAffineCoeffSteps fp v k hk) := by
  let rho : ℝ := 1 + 3 * fp.u ^ 2
  let R : ℝ := 2 * fp.u + 12 * fp.u ^ 2
  let E : ℕ → ℝ := fun j =>
    if hj : j < k then
      (kahanInputAbsMajorant fp v j
        (Nat.le_trans (Nat.le_of_lt hj) hk)).e
    else 0
  have hrho : 0 ≤ rho := by
    dsimp [rho]
    nlinarith [sq_nonneg fp.u]
  have hE : ∀ j, 0 ≤ E j := by
    intro j
    dsimp [E]
    by_cases hj : j < k
    · simp [hj, (kahanInputAbsMajorant_nonneg fp v j
        (Nat.le_trans (Nat.le_of_lt hj) hk)).2]
    · simp [hj]
  have hA : ∀ step ∈ kahanAffineCoeffSteps fp v k hk, |step.A| ≤ rho := by
    intro step hmem
    dsimp [rho]
    exact kahanAffineCoeffSteps_A_abs_le_one_plus_three_u_sq
      fp v k hk hu1 step hmem
  have hC :
      ∀ j (hj : j < (kahanAffineCoeffSteps fp v k hk).length),
        |((kahanAffineCoeffSteps fp v k hk).get ⟨j, hj⟩).correctionSource| ≤
          R * E j := by
    intro j hj
    have hjk : j < k := by
      simpa [kahanAffineCoeffSteps] using hj
    let idx : Fin n := ⟨j, Nat.lt_of_lt_of_le hjk hk⟩
    have hget :
        (kahanAffineCoeffSteps fp v k hk).get ⟨j, hj⟩ =
          kahanAffineCoeffStepOfIndex fp v idx := by
      simp [kahanAffineCoeffSteps, idx]
    have hbound :=
      kahanAffineCoeffStepOfIndex_correctionSource_abs_le_inputMajorant
        fp v idx hu1
    dsimp [R, E]
    change
      |((kahanAffineCoeffSteps fp v k hk).get ⟨j, hj⟩).correctionSource| ≤
        (2 * fp.u + 12 * fp.u ^ 2) *
          (if hj : j < k then
            (kahanInputAbsMajorant fp v j
              (Nat.le_trans (Nat.le_of_lt hj) hk)).e
          else 0)
    rw [hget]
    simpa [idx, hjk] using hbound
  simpa [rho, R, E] using
    kahanAffineCorrectionAbsUnroll_le_indexedBudget
      (rho := rho) (R := R) hrho E hE
      (kahanAffineCoeffSteps fp v k hk) hA hC

/-- The list fold over indexed Kahan affine coefficient steps is the matching
`Fin.foldl` prefix recurrence. -/
theorem kahanAffineCoeffSteps_fold_eq_finFold
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) (init : ℝ) :
    kahanAffineResidualFold (kahanAffineCoeffSteps fp v k hk) init =
      Fin.foldl k
        (fun total i =>
          let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
          let step := kahanAffineCoeffStepOfIndex fp v idx
          step.A * total + step.source)
        init := by
  dsimp [kahanAffineResidualFold, kahanAffineCoeffSteps]
  rw [list_foldl_ofFn_eq_fin_foldl]

/-- The residual-aware affine coefficient recurrence over the first `k`
actual Kahan prefix-trace steps produces the compensated prefix total. -/
theorem kahanAffineCoeffSteps_finFold_eq_prefix_total
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      Fin.foldl k
        (fun total i =>
          let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
          let step := kahanAffineCoeffStepOfIndex fp v idx
          step.A * total + step.source)
        0 =
      (kahanPrefixState fp v k hk).s +
        (kahanPrefixState fp v k hk).e
  | 0, _hk => by
      simp [kahanPrefixState, KahanState.zero]
  | k + 1, hk => by
      have hprev_le : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let idx : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let prev := kahanPrefixState fp v k hprev_le
      let step := kahanAffineCoeffStepOfIndex fp v idx
      have hih :=
        kahanAffineCoeffSteps_finFold_eq_prefix_total fp v k hprev_le
      have hih' :
          Fin.foldl k
            (fun total i =>
              let idx : Fin n := ⟨(i.castSucc).val,
                Nat.lt_of_lt_of_le (i.castSucc).isLt hk⟩
              let step := kahanAffineCoeffStepOfIndex fp v idx
              step.A * total + step.source)
            0 = prev.s + prev.e := by
        simpa [prev] using hih
      have hfoldPrefix :
          kahanPrefixState fp v (k + 1) hk =
            kahanStep fp (v idx) prev := by
        unfold kahanPrefixState
        rw [Fin.foldl_succ_last]
        rfl
      have hstep :
          (kahanStep fp (v idx) prev).s +
              (kahanStep fp (v idx) prev).e =
            step.A * (prev.s + prev.e) + step.source := by
        have htrace := kahanTrace_total_eq_affineCoeffStep fp v idx
        dsimp at htrace
        simpa [idx, prev, step, kahanTrace, kahanStep,
          KahanStepTrace.nextState] using htrace
      rw [Fin.foldl_succ_last]
      rw [hih']
      rw [hfoldPrefix, hstep]
      simp [step]
      ring

/-- The list of residual-aware affine coefficient steps for the first `k`
actual Kahan steps folds from zero to the compensated prefix total. -/
theorem kahanAffineCoeffSteps_fold_zero_eq_prefix_total
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    kahanAffineResidualFold (kahanAffineCoeffSteps fp v k hk) 0 =
      (kahanPrefixState fp v k hk).s +
        (kahanPrefixState fp v k hk).e := by
  rw [kahanAffineCoeffSteps_fold_eq_finFold]
  exact kahanAffineCoeffSteps_finFold_eq_prefix_total fp v k hk

/-- Concrete Kahan prefix version of the per-input coefficient residual bound.

For the first `k` Algorithm 4.2 steps, the compensated prefix total `s_k+e_k`
differs from the sum of source inputs multiplied by the product-form input
coefficients only by the propagated retained-correction contribution.  That
contribution is bounded by the input-only correction budget closed in the
previous dependency. -/
theorem kahanAffineCoeffSteps_prefixTotal_sub_sum_inputCoeff_abs_le_inputMajorantBudget
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (hu1 : fp.u ≤ 1) :
    let steps := kahanAffineCoeffSteps fp v k hk
    |((kahanPrefixState fp v k hk).s +
        (kahanPrefixState fp v k hk).e) -
      (∑ i : Fin steps.length,
        (steps.get i).x * (1 + kahanAffineInputCoeff steps i))| ≤
      kahanAffineCorrectionIndexedBudget
        (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
        (fun j =>
          if hj : j < k then
            (kahanInputAbsMajorant fp v j
              (Nat.le_trans (Nat.le_of_lt hj) hk)).e
          else 0)
        steps := by
  dsimp
  let steps := kahanAffineCoeffSteps fp v k hk
  have hfold :
      kahanAffineResidualFold steps 0 =
        (kahanPrefixState fp v k hk).s +
          (kahanPrefixState fp v k hk).e := by
    simpa [steps] using
      kahanAffineCoeffSteps_fold_zero_eq_prefix_total fp v k hk
  have hgeneric :=
    kahanAffineResidualFold_zero_sub_sum_inputCoeff_abs_le steps
  have hbudget :
      kahanAffineCorrectionAbsUnroll steps ≤
        kahanAffineCorrectionIndexedBudget
          (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
          (fun j =>
            if hj : j < k then
              (kahanInputAbsMajorant fp v j
                (Nat.le_trans (Nat.le_of_lt hj) hk)).e
            else 0)
          steps := by
    simpa [steps] using
      kahanAffineCoeffSteps_correctionAbsUnroll_le_inputMajorantBudget
        fp v k hk hu1
  calc
    |((kahanPrefixState fp v k hk).s +
        (kahanPrefixState fp v k hk).e) -
      (∑ i : Fin steps.length,
        (steps.get i).x * (1 + kahanAffineInputCoeff steps i))|
        = |kahanAffineResidualFold steps 0 -
            (∑ i : Fin steps.length,
              (steps.get i).x * (1 + kahanAffineInputCoeff steps i))| := by
            rw [hfold]
    _ ≤ kahanAffineCorrectionAbsUnroll steps := hgeneric
    _ ≤ kahanAffineCorrectionIndexedBudget
          (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
          (fun j =>
            if hj : j < k then
              (kahanInputAbsMajorant fp v j
                (Nat.le_trans (Nat.le_of_lt hj) hk)).e
            else 0)
          steps := hbudget

/-- Exact coefficient representation for the compensated prefix total after
absorbing the propagated retained-correction residual.

This is the first residual-absorption form for the C4.5 Knuth/Kahan route:
the previous theorem gives an additive residual bound around the explicit
product-form input coefficients; this theorem distributes that residual across
the source inputs as sign-aligned coefficient increments.  The remaining work
for (4.8) is to bound the product-form input coefficients themselves and
collapse the displayed radius. -/
theorem kahanAffineCoeffSteps_prefixTotal_exists_mu_inputCoeffResidual
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (hu1 : fp.u ≤ 1)
    (hinputAbs :
      0 < ∑ i : Fin (kahanAffineCoeffSteps fp v k hk).length,
        |((kahanAffineCoeffSteps fp v k hk).get i).x|) :
    let steps := kahanAffineCoeffSteps fp v k hk
    ∃ μ : Fin steps.length → ℝ,
      (∀ i,
        |μ i - kahanAffineInputCoeff steps i| ≤
          kahanAffineCorrectionIndexedBudget
            (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
            (fun j =>
              if hj : j < k then
                (kahanInputAbsMajorant fp v j
                  (Nat.le_trans (Nat.le_of_lt hj) hk)).e
              else 0)
            steps /
            (∑ j : Fin steps.length, |(steps.get j).x|)) ∧
        (kahanPrefixState fp v k hk).s +
          (kahanPrefixState fp v k hk).e =
          ∑ i : Fin steps.length, (steps.get i).x * (1 + μ i) := by
  dsimp
  let steps := kahanAffineCoeffSteps fp v k hk
  let budget :=
    kahanAffineCorrectionIndexedBudget
      (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
      (fun j =>
        if hj : j < k then
          (kahanInputAbsMajorant fp v j
            (Nat.le_trans (Nat.le_of_lt hj) hk)).e
        else 0)
      steps
  have hres :
      |((kahanPrefixState fp v k hk).s +
          (kahanPrefixState fp v k hk).e) -
        (∑ i : Fin steps.length,
          (steps.get i).x * (1 + kahanAffineInputCoeff steps i))| ≤
        budget := by
    simpa [steps, budget] using
      kahanAffineCoeffSteps_prefixTotal_sub_sum_inputCoeff_abs_le_inputMajorantBudget
        fp v k hk hu1
  have hinputAbs' :
      0 < ∑ i : Fin steps.length, |(steps.get i).x| := by
    simpa [steps] using hinputAbs
  simpa [steps, budget] using
    exists_summation_coefficients_of_abs_sub_sum_coeff_le
      (fun i : Fin steps.length => (steps.get i).x)
      (fun i : Fin steps.length => kahanAffineInputCoeff steps i)
      hres hinputAbs'

/-- Returned-prefix-sum version of the input-coefficient residual bound.

The source equation (4.8) is stated for the computed sum `s`, not merely for
the compensated total `s+e`.  This theorem charges the final retained
correction by the input-only correction majorant and therefore turns the
`s+e` residual bridge into an additive residual bound for the actual stored
prefix sum. -/
theorem kahanAffineCoeffSteps_prefixSum_sub_sum_inputCoeff_abs_le_inputMajorantBudget
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (hu1 : fp.u ≤ 1) :
    let steps := kahanAffineCoeffSteps fp v k hk
    |(kahanPrefixState fp v k hk).s -
      (∑ i : Fin steps.length,
        (steps.get i).x * (1 + kahanAffineInputCoeff steps i))| ≤
      kahanAffineCorrectionIndexedBudget
        (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
        (fun j =>
          if hj : j < k then
            (kahanInputAbsMajorant fp v j
              (Nat.le_trans (Nat.le_of_lt hj) hk)).e
          else 0)
        steps +
        (kahanInputAbsMajorant fp v k hk).e := by
  dsimp
  let steps := kahanAffineCoeffSteps fp v k hk
  let coeffSum : ℝ :=
    ∑ i : Fin steps.length,
      (steps.get i).x * (1 + kahanAffineInputCoeff steps i)
  let budget :=
    kahanAffineCorrectionIndexedBudget
      (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
      (fun j =>
        if hj : j < k then
          (kahanInputAbsMajorant fp v j
            (Nat.le_trans (Nat.le_of_lt hj) hk)).e
        else 0)
      steps
  have htotal :
      |((kahanPrefixState fp v k hk).s +
          (kahanPrefixState fp v k hk).e) - coeffSum| ≤ budget := by
    simpa [steps, coeffSum, budget] using
      kahanAffineCoeffSteps_prefixTotal_sub_sum_inputCoeff_abs_le_inputMajorantBudget
        fp v k hk hu1
  have he :
      |(kahanPrefixState fp v k hk).e| ≤
        (kahanInputAbsMajorant fp v k hk).e :=
    kahanPrefixState_e_abs_le_inputMajorant fp v k hk
  calc
    |(kahanPrefixState fp v k hk).s - coeffSum|
        = |(((kahanPrefixState fp v k hk).s +
              (kahanPrefixState fp v k hk).e) - coeffSum) -
            (kahanPrefixState fp v k hk).e| := by
            ring_nf
    _ ≤ |((kahanPrefixState fp v k hk).s +
            (kahanPrefixState fp v k hk).e) - coeffSum| +
          |(kahanPrefixState fp v k hk).e| := by
            simpa [sub_eq_add_neg, abs_neg] using
              abs_add_le
                (((kahanPrefixState fp v k hk).s +
                    (kahanPrefixState fp v k hk).e) - coeffSum)
                (-(kahanPrefixState fp v k hk).e)
    _ ≤ budget + (kahanInputAbsMajorant fp v k hk).e :=
          add_le_add htotal he

/-- Exact coefficient representation for the actual returned prefix sum after
absorbing both the propagated retained-correction residual and the final
retained correction.

This is the source-facing residual-absorption dependency for Higham (4.8):
the returned stored sum `s` is now expressed exactly as a coefficient
perturbation of the source inputs.  The coefficient increment beyond
`kahanAffineInputCoeff` is bounded by the propagated residual budget plus the
input-only final-correction majorant, normalized by `sum |x_i|`. -/
theorem kahanAffineCoeffSteps_prefixSum_exists_mu_inputCoeffResidual
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (hu1 : fp.u ≤ 1)
    (hinputAbs :
      0 < ∑ i : Fin (kahanAffineCoeffSteps fp v k hk).length,
        |((kahanAffineCoeffSteps fp v k hk).get i).x|) :
    let steps := kahanAffineCoeffSteps fp v k hk
    ∃ μ : Fin steps.length → ℝ,
      (∀ i,
        |μ i - kahanAffineInputCoeff steps i| ≤
          (kahanAffineCorrectionIndexedBudget
            (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
            (fun j =>
              if hj : j < k then
                (kahanInputAbsMajorant fp v j
                  (Nat.le_trans (Nat.le_of_lt hj) hk)).e
              else 0)
            steps +
            (kahanInputAbsMajorant fp v k hk).e) /
            (∑ j : Fin steps.length, |(steps.get j).x|)) ∧
        (kahanPrefixState fp v k hk).s =
          ∑ i : Fin steps.length, (steps.get i).x * (1 + μ i) := by
  dsimp
  let steps := kahanAffineCoeffSteps fp v k hk
  let budget :=
    kahanAffineCorrectionIndexedBudget
      (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
      (fun j =>
        if hj : j < k then
          (kahanInputAbsMajorant fp v j
            (Nat.le_trans (Nat.le_of_lt hj) hk)).e
        else 0)
      steps +
      (kahanInputAbsMajorant fp v k hk).e
  have hres :
      |(kahanPrefixState fp v k hk).s -
        (∑ i : Fin steps.length,
          (steps.get i).x * (1 + kahanAffineInputCoeff steps i))| ≤
        budget := by
    simpa [steps, budget] using
      kahanAffineCoeffSteps_prefixSum_sub_sum_inputCoeff_abs_le_inputMajorantBudget
        fp v k hk hu1
  have hinputAbs' :
      0 < ∑ i : Fin steps.length, |(steps.get i).x| := by
    simpa [steps] using hinputAbs
  simpa [steps, budget] using
    exists_summation_coefficients_of_abs_sub_sum_coeff_le
      (fun i : Fin steps.length => (steps.get i).x)
      (fun i : Fin steps.length => kahanAffineInputCoeff steps i)
      hres hinputAbs'

/-- Returned-prefix-sum coefficient witnesses with the product-form input
coefficient radius made explicit.

This combines the exact residual-absorption theorem with the bound on
`kahanAffineInputCoeff`.  The remaining C4.5 work is to collapse the displayed
product radius and the normalized residual budget to the source-shaped
`2*u + C*n*u^2` form. -/
theorem kahanAffineCoeffSteps_prefixSum_exists_mu_abs_le_productRadius
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (hu1 : fp.u ≤ 1)
    (hinputAbs :
      0 < ∑ i : Fin (kahanAffineCoeffSteps fp v k hk).length,
        |((kahanAffineCoeffSteps fp v k hk).get i).x|) :
    let steps := kahanAffineCoeffSteps fp v k hk
    ∃ μ : Fin steps.length → ℝ,
      (∀ i,
        |μ i| ≤
          kahanAffineInputCoeffProductRadius fp steps i +
            (kahanAffineCorrectionIndexedBudget
              (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
              (fun j =>
                if hj : j < k then
                  (kahanInputAbsMajorant fp v j
                    (Nat.le_trans (Nat.le_of_lt hj) hk)).e
                else 0)
              steps +
              (kahanInputAbsMajorant fp v k hk).e) /
              (∑ j : Fin steps.length, |(steps.get j).x|)) ∧
        (kahanPrefixState fp v k hk).s =
          ∑ i : Fin steps.length, (steps.get i).x * (1 + μ i) := by
  dsimp
  let steps := kahanAffineCoeffSteps fp v k hk
  let residual :=
    (kahanAffineCorrectionIndexedBudget
      (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
      (fun j =>
        if hj : j < k then
          (kahanInputAbsMajorant fp v j
            (Nat.le_trans (Nat.le_of_lt hj) hk)).e
        else 0)
      steps +
      (kahanInputAbsMajorant fp v k hk).e) /
      (∑ j : Fin steps.length, |(steps.get j).x|)
  obtain ⟨μ, hμdiff, hμeq⟩ :=
    kahanAffineCoeffSteps_prefixSum_exists_mu_inputCoeffResidual
      fp v k hk hu1 hinputAbs
  refine ⟨μ, ?_, ?_⟩
  · intro i
    have hcoeff :
        |kahanAffineInputCoeff steps i| ≤
          kahanAffineInputCoeffProductRadius fp steps i := by
      simpa [steps] using
        kahanAffineCoeffSteps_inputCoeff_abs_le_productRadius
          fp v k hk hu1 i
    have hdiff :
        |μ i - kahanAffineInputCoeff steps i| ≤ residual := by
      simpa [steps, residual] using hμdiff i
    calc
      |μ i| =
          |(μ i - kahanAffineInputCoeff steps i) +
            kahanAffineInputCoeff steps i| := by ring_nf
      _ ≤ |μ i - kahanAffineInputCoeff steps i| +
            |kahanAffineInputCoeff steps i| := abs_add_le _ _
      _ ≤ residual +
            kahanAffineInputCoeffProductRadius fp steps i := by
          exact add_le_add hdiff hcoeff
      _ =
          kahanAffineInputCoeffProductRadius fp steps i + residual := by
          ring
  · simpa [steps] using hμeq

/-- Source-shaped returned-prefix Kahan backward-error bridge from a product
radius and a source-scaled retained-correction residual budget.

This is the residual-budget version of the affine Goldberg/Knuth route: if the
product-form current-input coefficients are bounded by `P` and the remaining
retained-correction contribution is at most `D * sum_i |x_i|`, then the actual
stored prefix sum has exact source coefficients bounded by `P + D`. -/
theorem kahanAffineCoeffSteps_prefixSum_exists_mu_abs_le_of_productRadius_and_residualBudget
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (hu1 : fp.u ≤ 1)
    {P D : ℝ}
    (hP :
      let steps := kahanAffineCoeffSteps fp v k hk
      ∀ i : Fin steps.length,
        kahanAffineInputCoeffProductRadius fp steps i ≤ P)
    (hD_nonneg : 0 ≤ D)
    (hResidual :
      let steps := kahanAffineCoeffSteps fp v k hk
      kahanAffineCorrectionIndexedBudget
          (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
          (fun j =>
            if hj : j < k then
              (kahanInputAbsMajorant fp v j
                (Nat.le_trans (Nat.le_of_lt hj) hk)).e
            else 0)
          steps +
          (kahanInputAbsMajorant fp v k hk).e ≤
        D * (∑ j : Fin steps.length, |(steps.get j).x|)) :
    let steps := kahanAffineCoeffSteps fp v k hk
    ∃ μ : Fin steps.length → ℝ,
      (∀ i, |μ i| ≤ P + D) ∧
        (kahanPrefixState fp v k hk).s =
          ∑ i : Fin steps.length, (steps.get i).x * (1 + μ i) := by
  dsimp
  let steps := kahanAffineCoeffSteps fp v k hk
  let base : ℝ :=
    ∑ i : Fin steps.length,
      (steps.get i).x * (1 + kahanAffineInputCoeff steps i)
  let residualBudget : ℝ :=
    kahanAffineCorrectionIndexedBudget
      (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
      (fun j =>
        if hj : j < k then
          (kahanInputAbsMajorant fp v j
            (Nat.le_trans (Nat.le_of_lt hj) hk)).e
        else 0)
      steps +
      (kahanInputAbsMajorant fp v k hk).e
  let r : ℝ := (kahanPrefixState fp v k hk).s - base
  have hres0 : |r| ≤ residualBudget := by
    dsimp [r, base, residualBudget]
    simpa [steps] using
      kahanAffineCoeffSteps_prefixSum_sub_sum_inputCoeff_abs_le_inputMajorantBudget
        fp v k hk hu1
  have hResidual' :
      residualBudget ≤
        D * (∑ j : Fin steps.length, |(steps.get j).x|) := by
    simpa [steps, residualBudget] using hResidual
  have hres :
      |r| ≤ D * (∑ j : Fin steps.length, |(steps.get j).x|) :=
    hres0.trans hResidual'
  obtain ⟨η, hη, hηeq⟩ :=
    exists_summation_source_coefficients_of_abs_le_mul_sum_abs
      (fun i : Fin steps.length => (steps.get i).x)
      hD_nonneg hres
  let μ : Fin steps.length → ℝ :=
    fun i => kahanAffineInputCoeff steps i + η i
  refine ⟨μ, ?_, ?_⟩
  · intro i
    have hcoeff0 :
        |kahanAffineInputCoeff steps i| ≤
          kahanAffineInputCoeffProductRadius fp steps i := by
      simpa [steps] using
        kahanAffineCoeffSteps_inputCoeff_abs_le_productRadius
          fp v k hk hu1 i
    have hcoeff :
        |kahanAffineInputCoeff steps i| ≤ P := by
      exact hcoeff0.trans (by simpa [steps] using hP i)
    calc
      |μ i| =
          |kahanAffineInputCoeff steps i + η i| := by rfl
      _ ≤ |kahanAffineInputCoeff steps i| + |η i| := abs_add_le _ _
      _ ≤ P + D := add_le_add hcoeff (hη i)
  · have hηeq' :
        r = ∑ i : Fin steps.length, (steps.get i).x * η i := by
      simpa using hηeq
    calc
      (kahanPrefixState fp v k hk).s = base + r := by
        dsimp [r]
        ring
      _ = base + ∑ i : Fin steps.length, (steps.get i).x * η i := by
        rw [hηeq']
      _ = ∑ i : Fin steps.length, (steps.get i).x * (1 + μ i) := by
        dsimp [base, μ]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        ring

/-- Bound for the `y` operation's delta in the `i`th Kahan trace step. -/
theorem kahanTrace_deltaWitness_deltaY_bound (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    |(kahanTrace_deltaWitness fp v i).deltaY| ≤ fp.u :=
  (kahanTrace_deltaWitness fp v i).h_deltaY

/-- Bound for the `s` operation's delta in the `i`th Kahan trace step. -/
theorem kahanTrace_deltaWitness_deltaS_bound (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    |(kahanTrace_deltaWitness fp v i).deltaS| ≤ fp.u :=
  (kahanTrace_deltaWitness fp v i).h_deltaS

/-- Bound for the `temp - s` subtraction delta in the `i`th Kahan trace step. -/
theorem kahanTrace_deltaWitness_deltaSub_bound (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    |(kahanTrace_deltaWitness fp v i).deltaSub| ≤ fp.u :=
  (kahanTrace_deltaWitness fp v i).h_deltaSub

/-- Bound for the correction-addition delta in the `i`th Kahan trace step. -/
theorem kahanTrace_deltaWitness_deltaE_bound (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    |(kahanTrace_deltaWitness fp v i).deltaE| ≤ fp.u :=
  (kahanTrace_deltaWitness fp v i).h_deltaE

/-- The per-index finite-format Kahan step trace, with the input state obtained
by running all earlier finite-format steps. -/
noncomputable def finiteKahanTrace (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) : KahanStepTrace :=
  finiteKahanStepTrace fmt (v i)
    (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt))

/-- Final Kahan state after processing all `n` inputs. -/
noncomputable def fl_kahanState (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) : KahanState :=
  kahanPrefixState fp v n (Nat.le_refl n)

/-- Final finite-format Kahan state after processing all `n` inputs. -/
noncomputable def finiteKahanState (fmt : FloatingPointFormat) (n : ℕ)
    (v : Fin n → ℝ) : KahanState :=
  finiteKahanPrefixState fmt v n (Nat.le_refl n)

/-- Final compensated-summation value returned by Algorithm 4.2. -/
noncomputable def fl_kahanSum (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  (fl_kahanState fp n v).s

/-- Final finite-format compensated-summation value returned by Algorithm 4.2. -/
noncomputable def finiteKahanSum (fmt : FloatingPointFormat) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  (finiteKahanState fmt n v).s

/-- Final correction term retained by Algorithm 4.2. -/
noncomputable def fl_kahanCorrection (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  (fl_kahanState fp n v).e

/-- Final finite-format correction term retained by Algorithm 4.2. -/
noncomputable def finiteKahanCorrection (fmt : FloatingPointFormat) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  (finiteKahanState fmt n v).e

/-- The finite-format `y = fl(x+e)` value in one Kahan step is finite. -/
theorem finiteKahanStepTrace_y_finiteSystem
    (fmt : FloatingPointFormat) (x : ℝ) (state : KahanState) :
    fmt.finiteSystem (finiteKahanStepTrace fmt x state).y := by
  simpa [finiteKahanStepTrace] using
    fmt.finiteRoundToEvenOp_finiteSystem BasicOp.add x state.e

/-- The finite-format returned-sum coordinate in one Kahan step is finite. -/
theorem finiteKahanStepTrace_s_finiteSystem
    (fmt : FloatingPointFormat) (x : ℝ) (state : KahanState) :
    fmt.finiteSystem (finiteKahanStepTrace fmt x state).s := by
  simpa [finiteKahanStepTrace] using
    fmt.finiteRoundToEvenOp_finiteSystem BasicOp.add state.s
      (fmt.finiteRoundToEvenOp BasicOp.add x state.e)

/-- The finite-format retained-correction coordinate in one Kahan step is
finite. -/
theorem finiteKahanStepTrace_e_finiteSystem
    (fmt : FloatingPointFormat) (x : ℝ) (state : KahanState) :
    fmt.finiteSystem (finiteKahanStepTrace fmt x state).e := by
  simpa [finiteKahanStepTrace] using
    fmt.finiteRoundToEvenOp_finiteSystem BasicOp.add
      (fmt.finiteRoundToEvenOp BasicOp.sub state.s
        (fmt.finiteRoundToEvenOp BasicOp.add state.s
          (fmt.finiteRoundToEvenOp BasicOp.add x state.e)))
      (fmt.finiteRoundToEvenOp BasicOp.add x state.e)

/-- One finite-format Kahan persistent-state update has finite coordinates. -/
theorem finiteKahanStep_finiteSystem
    (fmt : FloatingPointFormat) (x : ℝ) (state : KahanState) :
    fmt.finiteSystem (finiteKahanStep fmt x state).s ∧
      fmt.finiteSystem (finiteKahanStep fmt x state).e := by
  constructor
  · simpa [finiteKahanStep, KahanStepTrace.nextState] using
      finiteKahanStepTrace_s_finiteSystem fmt x state
  · simpa [finiteKahanStep, KahanStepTrace.nextState] using
      finiteKahanStepTrace_e_finiteSystem fmt x state

/-- Every finite-format Kahan prefix state has finite coordinates. -/
theorem finiteKahanPrefixState_finiteSystem
    (fmt : FloatingPointFormat) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      fmt.finiteSystem (finiteKahanPrefixState fmt v k hk).s ∧
        fmt.finiteSystem (finiteKahanPrefixState fmt v k hk).e
  | 0, _hk => by
      simp [finiteKahanPrefixState, KahanState.zero, fmt.finiteSystem_zero]
  | k + 1, hk => by
      have hprev_le : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let idx : Fin n :=
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let prev := finiteKahanPrefixState fmt v k hprev_le
      have hfold :
          finiteKahanPrefixState fmt v (k + 1) hk =
            finiteKahanStep fmt (v idx) prev := by
        unfold finiteKahanPrefixState
        rw [Fin.foldl_succ_last]
        rfl
      rw [hfold]
      exact finiteKahanStep_finiteSystem fmt (v idx) prev

/-- Stored-sum projection of `finiteKahanPrefixState_finiteSystem`. -/
theorem finiteKahanPrefixState_s_finiteSystem
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    fmt.finiteSystem (finiteKahanPrefixState fmt v k hk).s :=
  (finiteKahanPrefixState_finiteSystem fmt v k hk).1

/-- Retained-correction projection of `finiteKahanPrefixState_finiteSystem`. -/
theorem finiteKahanPrefixState_e_finiteSystem
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    fmt.finiteSystem (finiteKahanPrefixState fmt v k hk).e :=
  (finiteKahanPrefixState_finiteSystem fmt v k hk).2

/-- The `temp` coordinate in every finite-format Kahan trace step is finite. -/
theorem finiteKahanTrace_temp_finiteSystem
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    fmt.finiteSystem (finiteKahanTrace fmt v i).temp := by
  simpa [finiteKahanTrace, finiteKahanStepTrace] using
    finiteKahanPrefixState_s_finiteSystem
      fmt v i.val (Nat.le_of_lt i.isLt)

/-- The `y` coordinate in every finite-format Kahan trace step is finite. -/
theorem finiteKahanTrace_y_finiteSystem
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    fmt.finiteSystem (finiteKahanTrace fmt v i).y := by
  simpa [finiteKahanTrace] using
    finiteKahanStepTrace_y_finiteSystem fmt (v i)
      (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt))

/-- The returned-sum coordinate in every finite-format Kahan trace step is
finite. -/
theorem finiteKahanTrace_s_finiteSystem
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    fmt.finiteSystem (finiteKahanTrace fmt v i).s := by
  simpa [finiteKahanTrace] using
    finiteKahanStepTrace_s_finiteSystem fmt (v i)
      (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt))

/-- Add/sub realization of a concrete finite round-to-even format by the
abstract `FPModel` operations used in Algorithm 4.2.

The Kahan returned-sum theorem is stated for `FPModel`, while the exact
subtraction obligations are naturally finite-format facts.  This small bridge
records only the two primitive operations needed to identify the abstract
Kahan trace with the finite round-to-even trace. -/
structure KahanAddSubFiniteRoundToEvenRealization
    (fp : FPModel) (fmt : FloatingPointFormat) : Prop where
  add :
    ∀ x y : ℝ, fp.fl_add x y = fmt.finiteRoundToEvenOp BasicOp.add x y
  sub :
    ∀ x y : ℝ, fp.fl_sub x y = fmt.finiteRoundToEvenOp BasicOp.sub x y

/-- One abstract Kahan trace equals the corresponding finite round-to-even
trace when the model's add/sub primitives realize that finite format. -/
theorem kahanStepTrace_eq_finiteKahanStepTrace_of_addSubFiniteRoundToEven
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (x : ℝ) (state : KahanState) :
    kahanStepTrace fp x state = finiteKahanStepTrace fmt x state := by
  simp [kahanStepTrace, finiteKahanStepTrace, hround.add, hround.sub]

/-- Persistent-state version of
`kahanStepTrace_eq_finiteKahanStepTrace_of_addSubFiniteRoundToEven`. -/
theorem kahanStep_eq_finiteKahanStep_of_addSubFiniteRoundToEven
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (x : ℝ) (state : KahanState) :
    kahanStep fp x state = finiteKahanStep fmt x state := by
  simp [kahanStep, finiteKahanStep,
    kahanStepTrace_eq_finiteKahanStepTrace_of_addSubFiniteRoundToEven
      fp fmt hround x state]

/-- The abstract and finite Kahan prefix states agree when add/sub operations
are the same finite round-to-even operations. -/
theorem kahanPrefixState_eq_finiteKahanPrefixState_of_addSubFiniteRoundToEven
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      kahanPrefixState fp v k hk = finiteKahanPrefixState fmt v k hk
  | 0, _hk => by
      simp [kahanPrefixState, finiteKahanPrefixState, KahanState.zero]
  | k + 1, hk => by
      have hprev_le : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let idx : Fin n :=
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let prevFp := kahanPrefixState fp v k hprev_le
      let prevFinite := finiteKahanPrefixState fmt v k hprev_le
      have hih :
          prevFp = prevFinite := by
        simpa [prevFp, prevFinite] using
          kahanPrefixState_eq_finiteKahanPrefixState_of_addSubFiniteRoundToEven
            fp fmt hround v k hprev_le
      have hfoldFp :
          kahanPrefixState fp v (k + 1) hk =
            kahanStep fp (v idx) prevFp := by
        unfold kahanPrefixState
        rw [Fin.foldl_succ_last]
        rfl
      have hfoldFinite :
          finiteKahanPrefixState fmt v (k + 1) hk =
            finiteKahanStep fmt (v idx) prevFinite := by
        unfold finiteKahanPrefixState
        rw [Fin.foldl_succ_last]
        rfl
      rw [hfoldFp, hfoldFinite, hih]
      exact
        kahanStep_eq_finiteKahanStep_of_addSubFiniteRoundToEven
          fp fmt hround (v idx) prevFinite

/-- Per-index abstract Kahan traces agree with the finite round-to-even traces
under add/sub realization. -/
theorem kahanTrace_eq_finiteKahanTrace_of_addSubFiniteRoundToEven
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    kahanTrace fp v i = finiteKahanTrace fmt v i := by
  unfold kahanTrace finiteKahanTrace
  have hprefix :=
    kahanPrefixState_eq_finiteKahanPrefixState_of_addSubFiniteRoundToEven
      fp fmt hround v i.val (Nat.le_of_lt i.isLt)
  rw [hprefix]
  exact
    kahanStepTrace_eq_finiteKahanStepTrace_of_addSubFiniteRoundToEven
      fp fmt hround (v i)
      (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt))

/-- Finite-format representability surface for the displayed Kahan correction
subtraction `temp - s` over a prefix. -/
def FiniteKahanPrefixCorrectionSubFinite
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : Prop :=
  ∀ i : Fin k,
    let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    fmt.finiteSystem
      ((finiteKahanTrace fmt v idx).temp - (finiteKahanTrace fmt v idx).s)

/-- First-step split for the direct finite-subtraction route.

At index `0`, the Kahan trace has `temp = 0`, so `temp - s = -s` is finite
from the rounded trace itself.  Consequently a direct tail proof of finite
representability for `temp - s` is enough for the whole prefix. -/
theorem FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_sub_finite
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hfiniteTail :
      ∀ i : Fin k, i.val ≠ 0 →
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        fmt.finiteSystem
          ((finiteKahanTrace fmt v idx).temp -
            (finiteKahanTrace fmt v idx).s)) :
    FiniteKahanPrefixCorrectionSubFinite fmt v k hk := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  change
    fmt.finiteSystem
      ((finiteKahanTrace fmt v idx).temp -
        (finiteKahanTrace fmt v idx).s)
  by_cases hi0 : i.val = 0
  · have hs : fmt.finiteSystem (finiteKahanTrace fmt v idx).s :=
      finiteKahanTrace_s_finiteSystem fmt v idx
    have htemp : (finiteKahanTrace fmt v idx).temp = 0 := by
      simp [finiteKahanTrace, finiteKahanStepTrace,
        finiteKahanPrefixState, KahanState.zero, idx, hi0]
    have hrewrite :
        (finiteKahanTrace fmt v idx).temp -
            (finiteKahanTrace fmt v idx).s =
          -((finiteKahanTrace fmt v idx).s) := by
      rw [htemp]
      ring
    rw [hrewrite]
    exact fmt.finiteSystem_neg hs
  · simpa [idx] using hfiniteTail i hi0

/-- Inclusive Sterbenz conditions on the displayed Kahan correction
subtractions provide the finite representability surface needed by the
exact-subtraction route. -/
theorem FiniteKahanPrefixCorrectionSubFinite.of_sterbenzRatioConditionLe
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hsterbenz :
      ∀ i : Fin k,
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        fmt.sterbenzRatioConditionLe
          (finiteKahanTrace fmt v idx).temp
          (finiteKahanTrace fmt v idx).s) :
    FiniteKahanPrefixCorrectionSubFinite fmt v k hk := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  exact
    fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioConditionLe
      (finiteKahanTrace_temp_finiteSystem fmt v idx)
      (finiteKahanTrace_s_finiteSystem fmt v idx)
      (by simpa [idx] using hsterbenz i)

/-- Inclusive Ferguson exponent conditions on the displayed Kahan correction
subtractions provide the same finite representability surface.  This exposes a
non-FastTwoSum finite/coherence route for the remaining Eq. (4.8) bottleneck. -/
theorem FiniteKahanPrefixCorrectionSubFinite.of_fergusonConditionLe
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hferguson :
      ∀ i : Fin k,
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        fmt.fergusonExponentConditionLe
          (finiteKahanTrace fmt v idx).temp
          (finiteKahanTrace fmt v idx).s) :
    FiniteKahanPrefixCorrectionSubFinite fmt v k hk := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  have hnormal :
      fmt.normalizedSystem
        ((finiteKahanTrace fmt v idx).temp -
          (finiteKahanTrace fmt v idx).s) :=
    fmt.fergusonExponentConditionLe_sub_normalized
      (by simpa [idx] using hferguson i)
  exact Or.inr (Or.inl hnormal)

/-- First-step split for the inclusive Sterbenz finite-subtraction route.

At index `0`, the Kahan trace has `temp = 0`, so `temp - s = -s` is finite
from the rounded trace itself.  Only tail steps need an inclusive Sterbenz
condition on the displayed correction subtraction. -/
theorem FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_sterbenzLe
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hsterbenz :
      ∀ i : Fin k, i.val ≠ 0 →
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        fmt.sterbenzRatioConditionLe
          (finiteKahanTrace fmt v idx).temp
          (finiteKahanTrace fmt v idx).s) :
    FiniteKahanPrefixCorrectionSubFinite fmt v k hk := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  change
    fmt.finiteSystem
      ((finiteKahanTrace fmt v idx).temp - (finiteKahanTrace fmt v idx).s)
  by_cases hi0 : i.val = 0
  · have hs : fmt.finiteSystem (finiteKahanTrace fmt v idx).s :=
      finiteKahanTrace_s_finiteSystem fmt v idx
    have htemp : (finiteKahanTrace fmt v idx).temp = 0 := by
      simp [finiteKahanTrace, finiteKahanStepTrace,
        finiteKahanPrefixState, KahanState.zero, idx, hi0]
    have hrewrite :
        (finiteKahanTrace fmt v idx).temp -
            (finiteKahanTrace fmt v idx).s =
          -((finiteKahanTrace fmt v idx).s) := by
      rw [htemp]
      ring
    rw [hrewrite]
    exact fmt.finiteSystem_neg hs
  · exact
      fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioConditionLe
        (finiteKahanTrace_temp_finiteSystem fmt v idx)
        (finiteKahanTrace_s_finiteSystem fmt v idx)
        (by simpa [idx] using hsterbenz i hi0)

/-- First-step split for the inclusive Ferguson finite-subtraction route.

The first correction subtraction is finite because `temp = 0`; tail steps may
instead be discharged by Ferguson's exponent condition. -/
theorem FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_fergusonLe
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hferguson :
      ∀ i : Fin k, i.val ≠ 0 →
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        fmt.fergusonExponentConditionLe
          (finiteKahanTrace fmt v idx).temp
          (finiteKahanTrace fmt v idx).s) :
    FiniteKahanPrefixCorrectionSubFinite fmt v k hk := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  change
    fmt.finiteSystem
      ((finiteKahanTrace fmt v idx).temp - (finiteKahanTrace fmt v idx).s)
  by_cases hi0 : i.val = 0
  · have hs : fmt.finiteSystem (finiteKahanTrace fmt v idx).s :=
      finiteKahanTrace_s_finiteSystem fmt v idx
    have htemp : (finiteKahanTrace fmt v idx).temp = 0 := by
      simp [finiteKahanTrace, finiteKahanStepTrace,
        finiteKahanPrefixState, KahanState.zero, idx, hi0]
    have hrewrite :
        (finiteKahanTrace fmt v idx).temp -
            (finiteKahanTrace fmt v idx).s =
          -((finiteKahanTrace fmt v idx).s) := by
      rw [htemp]
      ring
    rw [hrewrite]
    exact fmt.finiteSystem_neg hs
  · have hnormal :
        fmt.normalizedSystem
          ((finiteKahanTrace fmt v idx).temp -
            (finiteKahanTrace fmt v idx).s) :=
      fmt.fergusonExponentConditionLe_sub_normalized
        (by simpa [idx] using hferguson i hi0)
    exact Or.inr (Or.inl hnormal)

/-- Per-step FastTwoSum finite certificates for the Kahan correction formula
over a prefix.  The field `finite_a_sub_s` is exactly the representability
needed for the displayed subtraction in Algorithm 4.2. -/
def KahanPrefixFastTwoSumFiniteCertificates
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : Prop :=
  ∀ i : Fin k,
    let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    FastTwoSumFiniteCertificate fmt
      (finiteKahanTrace fmt v idx).temp
      (finiteKahanTrace fmt v idx).y

/-- Pointwise base-2 absolute-order FastTwoSum hypotheses supply the prefix
finite certificates needed by the Kahan exact-subtraction bridge. -/
theorem KahanPrefixFastTwoSumFiniteCertificates.of_base2_abs_gt
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hfiniteTemp :
      ∀ i : Fin k,
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        fmt.finiteSystem (finiteKahanTrace fmt v idx).temp)
    (hfiniteY :
      ∀ i : Fin k,
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        fmt.finiteSystem (finiteKahanTrace fmt v idx).y)
    (horder :
      ∀ i : Fin k,
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        |(finiteKahanTrace fmt v idx).y| <
          |(finiteKahanTrace fmt v idx).temp|)
    (hrange :
      ∀ i : Fin k,
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        fmt.finiteNormalRange
          ((finiteKahanTrace fmt v idx).temp +
            (finiteKahanTrace fmt v idx).y)) :
    KahanPrefixFastTwoSumFiniteCertificates fmt v k hk := by
  intro i
  exact
    FastTwoSumFiniteCertificate.of_base2_abs_gt
      fmt hbeta ht
      (hfiniteTemp i)
      (hfiniteY i)
      (horder i)
      (hrange i)

/-- Kahan-prefix FastTwoSum certificates with the initialized first step split
off.

At index `0`, the Kahan `temp` value is exactly zero, so the usual strict
absolute-order premise `|y| < |temp|` is not the right hypothesis.  The first
step instead uses exact finite zero-addition; the base-2 absolute-order and
normal-range hypotheses are required only for the tail steps. -/
theorem KahanPrefixFastTwoSumFiniteCertificates.of_first_exact_and_tail_base2_abs_gt
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (horder :
      ∀ i : Fin k, i.val ≠ 0 →
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        |(finiteKahanTrace fmt v idx).y| <
          |(finiteKahanTrace fmt v idx).temp|)
    (hrange :
      ∀ i : Fin k, i.val ≠ 0 →
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        fmt.finiteNormalRange
          ((finiteKahanTrace fmt v idx).temp +
            (finiteKahanTrace fmt v idx).y)) :
    KahanPrefixFastTwoSumFiniteCertificates fmt v k hk := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  by_cases hi0 : i.val = 0
  · have hy :
        fmt.finiteSystem (finiteKahanTrace fmt v idx).y :=
      finiteKahanTrace_y_finiteSystem fmt v idx
    have htemp : (finiteKahanTrace fmt v idx).temp = 0 := by
      simp [finiteKahanTrace, finiteKahanStepTrace,
        finiteKahanPrefixState, KahanState.zero, idx, hi0]
    have hadd :
        fmt.finiteRoundToEvenOp BasicOp.add
            (finiteKahanTrace fmt v idx).temp
            (finiteKahanTrace fmt v idx).y =
          (finiteKahanTrace fmt v idx).temp +
            (finiteKahanTrace fmt v idx).y := by
      rw [htemp]
      simpa using fmt.finiteRoundToEvenOp_add_zero_of_finiteSystem hy
    exact
      FastTwoSumFiniteCertificate.of_exact_add
        fmt (finiteKahanTrace fmt v idx).temp
          (finiteKahanTrace fmt v idx).y hy hadd
  · exact
      FastTwoSumFiniteCertificate.of_base2_abs_gt
        fmt hbeta ht
        (finiteKahanTrace_temp_finiteSystem fmt v idx)
        (finiteKahanTrace_y_finiteSystem fmt v idx)
        (by simpa [idx] using horder i hi0)
        (by simpa [idx] using hrange i hi0)

/-- A FastTwoSum finite certificate supplies the finite representability
needed by the Kahan displayed correction subtraction. -/
theorem FiniteKahanPrefixCorrectionSubFinite.of_fastTwoSumCertificates
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hcerts : KahanPrefixFastTwoSumFiniteCertificates fmt v k hk) :
    FiniteKahanPrefixCorrectionSubFinite fmt v k hk := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  have hcert :
      FastTwoSumFiniteCertificate fmt
        (finiteKahanTrace fmt v idx).temp
        (finiteKahanTrace fmt v idx).y := by
    simpa [KahanPrefixFastTwoSumFiniteCertificates, idx] using hcerts i
  have hs :
      (finiteKahanTrace fmt v idx).s =
        fmt.finiteRoundToEvenOp BasicOp.add
          (finiteKahanTrace fmt v idx).temp
          (finiteKahanTrace fmt v idx).y := by
    simp [finiteKahanTrace, finiteKahanStepTrace]
  simpa [FiniteKahanPrefixCorrectionSubFinite, idx, hs] using
    hcert.finite_a_sub_s

/-- Concrete finite-format representability of every correction subtraction
implies the abstract prefix exact-subtraction surface for Algorithm 4.2. -/
theorem KahanPrefixCorrectionSubExact.of_finiteRoundToEven_sub_finite
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hfinite : FiniteKahanPrefixCorrectionSubFinite fmt v k hk) :
    KahanPrefixCorrectionSubExact fp v k hk := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  have htrace :
      kahanTrace fp v idx = finiteKahanTrace fmt v idx :=
    kahanTrace_eq_finiteKahanTrace_of_addSubFiniteRoundToEven
      fp fmt hround v idx
  have hfin :
      fmt.finiteSystem
        ((finiteKahanTrace fmt v idx).temp -
          (finiteKahanTrace fmt v idx).s) := by
    simpa [FiniteKahanPrefixCorrectionSubFinite, idx] using hfinite i
  have hsubFinite :
      fmt.finiteRoundToEvenOp BasicOp.sub
          (finiteKahanTrace fmt v idx).temp
          (finiteKahanTrace fmt v idx).s =
        (finiteKahanTrace fmt v idx).temp -
          (finiteKahanTrace fmt v idx).s := by
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub)
        (x := (finiteKahanTrace fmt v idx).temp)
        (y := (finiteKahanTrace fmt v idx).s) hfin)
  have htarget :
      fp.fl_sub (kahanTrace fp v idx).temp (kahanTrace fp v idx).s =
        (kahanTrace fp v idx).temp - (kahanTrace fp v idx).s := by
    simpa [htrace, hround.sub] using hsubFinite
  simpa [KahanPrefixCorrectionSubExact, idx] using htarget

/-- FastTwoSum finite certificates imply the abstract prefix exact-subtraction
surface for the Kahan returned-sum theorem. -/
theorem KahanPrefixCorrectionSubExact.of_finiteRoundToEven_fastTwoSumCertificates
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hcerts : KahanPrefixFastTwoSumFiniteCertificates fmt v k hk) :
    KahanPrefixCorrectionSubExact fp v k hk :=
  KahanPrefixCorrectionSubExact.of_finiteRoundToEven_sub_finite
    fp fmt hround v k hk
    (FiniteKahanPrefixCorrectionSubFinite.of_fastTwoSumCertificates
      fmt v k hk hcerts)

/-- The final state is the explicit `n`-step prefix state. -/
theorem fl_kahanState_eq_prefixState (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) :
    fl_kahanState fp n v = kahanPrefixState fp v n (Nat.le_refl n) := by
  rfl

/-- The full indexed Kahan trace instantiates the residual-aware affine
coefficient recurrence for the final compensated total. -/
theorem kahanAffineCoeffSteps_fold_zero_eq_final_total
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) :
    kahanAffineResidualFold (kahanAffineCoeffSteps fp v n (Nat.le_refl n)) 0 =
      (fl_kahanState fp n v).s + (fl_kahanState fp n v).e := by
  simpa [fl_kahanState] using
    kahanAffineCoeffSteps_fold_zero_eq_prefix_total fp v n (Nat.le_refl n)

/-- The returned sum is the `s` field of the final state. -/
theorem fl_kahanSum_eq_state_s (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) :
    fl_kahanSum fp n v = (fl_kahanState fp n v).s := by
  rfl

/-- The retained correction is the `e` field of the final state. -/
theorem fl_kahanCorrection_eq_state_e (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) :
    fl_kahanCorrection fp n v = (fl_kahanState fp n v).e := by
  rfl

/-- Final returned-Kahan source bound from affine product smallness and a
source-scaled retained-correction budget.

The theorem packages the remaining Eq. (4.8) ordinary returned-sum work into a
single interpretable estimate: the propagated retained-correction budget must
be bounded by `C * n * u^2 * sum_i |x_i|`.  Under that estimate and the standard
small product condition, the returned Kahan sum has source coefficients with
radius `2*u + (9 + (72 + C)*n)*u^2`. -/
theorem fl_kahanSum_backward_error_source_bound_of_affine_residualBudget
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hu1 : fp.u ≤ 1)
    {C : ℝ} (hC_nonneg : 0 ≤ C)
    (hProductSmall : (n : ℝ) * (3 * fp.u ^ 2) ≤ 1 / 2)
    (hResidual :
      let steps := kahanAffineCoeffSteps fp v n (Nat.le_refl n)
      kahanAffineCorrectionIndexedBudget
          (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
          (fun j =>
            if hj : j < n then
              (kahanInputAbsMajorant fp v j (Nat.le_of_lt hj)).e
            else 0)
          steps +
          (kahanInputAbsMajorant fp v n (Nat.le_refl n)).e ≤
        (C * (n : ℝ) * fp.u ^ 2) *
          (∑ j : Fin steps.length, |(steps.get j).x|)) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + (9 + (72 + C) * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  let steps := kahanAffineCoeffSteps fp v n (Nat.le_refl n)
  let P : ℝ := 2 * fp.u + (9 + 72 * (n : ℝ)) * fp.u ^ 2
  let D : ℝ := C * (n : ℝ) * fp.u ^ 2
  have hlen : n = steps.length := by
    simp [steps, kahanAffineCoeffSteps]
  have hP :
      ∀ i : Fin steps.length,
        kahanAffineInputCoeffProductRadius fp steps i ≤ P := by
    intro i
    have hdrop_nat :
        (steps.drop (i.val + 1)).length ≤ steps.length := by
      rw [List.length_drop]
      exact Nat.sub_le steps.length (i.val + 1)
    have hdrop_le :
        ((steps.drop (i.val + 1)).length : ℝ) ≤ (n : ℝ) := by
      have hdrop_le_steps :
          ((steps.drop (i.val + 1)).length : ℝ) ≤
            (steps.length : ℝ) := by
        exact_mod_cast hdrop_nat
      have hsteps_len : (steps.length : ℝ) = (n : ℝ) := by
        exact_mod_cast hlen.symm
      rw [hsteps_len] at hdrop_le_steps
      exact hdrop_le_steps
    have hc_nonneg : 0 ≤ 3 * fp.u ^ 2 := by
      nlinarith [sq_nonneg fp.u]
    have hsmall_i :
        ((steps.drop (i.val + 1)).length : ℝ) *
            (3 * fp.u ^ 2) ≤ 1 / 2 := by
      have hmul := mul_le_mul_of_nonneg_right hdrop_le hc_nonneg
      exact hmul.trans hProductSmall
    have hlocal :=
      kahanAffineInputCoeffProductRadius_le_two_u_plus
        fp steps i hu1 hsmall_i
    have hcoef :
        9 + 72 * ((steps.drop (i.val + 1)).length : ℝ) ≤
          9 + 72 * (n : ℝ) := by
      nlinarith
    have hcoef_mul :
        (9 + 72 * ((steps.drop (i.val + 1)).length : ℝ)) *
            fp.u ^ 2 ≤
          (9 + 72 * (n : ℝ)) * fp.u ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg fp.u)
    dsimp [P]
    nlinarith
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg
      (mul_nonneg hC_nonneg (by exact_mod_cast Nat.zero_le n))
      (sq_nonneg fp.u)
  have hprefix :
      ∃ μs : Fin steps.length → ℝ,
        (∀ i, |μs i| ≤ P + D) ∧
          (kahanPrefixState fp v n (Nat.le_refl n)).s =
            ∑ i : Fin steps.length, (steps.get i).x * (1 + μs i) := by
    simpa [steps, P, D] using
      (kahanAffineCoeffSteps_prefixSum_exists_mu_abs_le_of_productRadius_and_residualBudget
        fp v n (Nat.le_refl n) hu1
        (P := P) (D := D)
        (by simpa [steps, P] using hP)
        hD_nonneg
        (by simpa [steps, D] using hResidual))
  obtain ⟨μSteps, hμSteps, hsumSteps⟩ := hprefix
  let idx : Fin n → Fin steps.length := fun i => finCongr hlen i
  let μ : Fin n → ℝ := fun i => μSteps (idx i)
  refine ⟨μ, ?_, ?_⟩
  · intro i
    have hcollapse :
        P + D =
          2 * fp.u + (9 + (72 + C) * (n : ℝ)) * fp.u ^ 2 := by
      dsimp [P, D]
      ring
    simpa [μ, hcollapse] using hμSteps (idx i)
  · have hsum_reindex :
        (∑ i : Fin n, v i * (1 + μ i)) =
          ∑ j : Fin steps.length,
            (steps.get j).x * (1 + μSteps j) := by
      refine Fintype.sum_equiv (finCongr hlen) _ _ ?_
      intro i
      dsimp [μ, idx]
      simp [steps, kahanAffineCoeffSteps, kahanAffineCoeffStepOfIndex]
    simpa [fl_kahanSum, fl_kahanState, steps] using
      hsumSteps.trans hsum_reindex.symm

/-- One-input obstruction to closing the current input-majorant affine
residual-budget route with a fixed second-order constant.

For exact arithmetic advertised with unit roundoff `u`, one input of magnitude
`1` has zero propagated indexed correction budget, but the final
input-majorant retained-correction term is
`u * (1 + u)^2 * (2 + u)`.  This cannot be bounded by `C*u^2` whenever
`C*u <= 1`. -/
theorem not_kahanAffine_residualBudget_inputMajorant_one_of_Cu_le_one
    (C u : ℝ) (hu_pos : 0 < u) (hCu_le_one : C * u ≤ 1) :
    let fp : FPModel := FPModel.exactWithUnitRoundoff u (le_of_lt hu_pos)
    let v : Fin 1 → ℝ := fun _ => 1
    ¬
      (let steps := kahanAffineCoeffSteps fp v 1 (Nat.le_refl 1)
       kahanAffineCorrectionIndexedBudget
          (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
          (fun j =>
            if hj : j < 1 then
              (kahanInputAbsMajorant fp v j (Nat.le_of_lt hj)).e
            else 0)
          steps +
          (kahanInputAbsMajorant fp v 1 (Nat.le_refl 1)).e ≤
        (C * (1 : ℝ) * fp.u ^ 2) *
          (∑ j : Fin steps.length, |(steps.get j).x|)) := by
  dsimp
  intro h
  norm_num [FPModel.exactWithUnitRoundoff, kahanAffineCoeffSteps,
    kahanAffineCoeffStepOfIndex, kahanAffineCorrectionIndexedBudget,
    kahanInputAbsMajorant] at h
  have hleft_lower :
      2 * u ≤ u * (1 + u) ^ 2 * (2 + u) := by
    have h1 : 1 ≤ (1 + u) ^ 2 := by
      nlinarith [hu_pos, sq_nonneg u]
    have h2 : 2 ≤ 2 + u := by
      linarith
    have hu_nonneg : 0 ≤ u := le_of_lt hu_pos
    calc
      2 * u = u * 1 * 2 := by ring
      _ ≤ u * (1 + u) ^ 2 * (2 + u) := by
          exact
            mul_le_mul
              (mul_le_mul_of_nonneg_left h1 hu_nonneg) h2
              (by norm_num)
              (mul_nonneg hu_nonneg
                (by nlinarith [hu_pos, sq_nonneg u]))
  have hrhs_le_u : C * u ^ 2 ≤ u := by
    have hmul :=
      mul_le_mul_of_nonneg_right hCu_le_one (le_of_lt hu_pos)
    nlinarith
  have htwo_le_one : 2 * u ≤ u :=
    hleft_lower.trans (h.trans hrhs_le_u)
  nlinarith

/-- No nonnegative fixed constant can make the current input-majorant affine
residual budget imply a second-order source-scaled estimate uniformly in small
advertised unit roundoffs.

This is a route-elimination theorem for the remaining Higham Chapter 4
equation (4.8) bottleneck.  The existing conditional wrapper
`fl_kahanSum_backward_error_source_bound_of_affine_residualBudget` is still
valid, but its residual-budget hypothesis cannot be discharged by the present
input-only majorant with a fixed `C*n*u^2*sum |x_i|` estimate. -/
theorem not_exists_kahanAffine_residualBudget_inputMajorant_fixed_C :
    ¬ ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : ℝ, ∀ (hu_pos : 0 < u), C * u ≤ 1 →
        let fp : FPModel := FPModel.exactWithUnitRoundoff u (le_of_lt hu_pos)
        let v : Fin 1 → ℝ := fun _ => 1
        let steps := kahanAffineCoeffSteps fp v 1 (Nat.le_refl 1)
        kahanAffineCorrectionIndexedBudget
            (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
            (fun j =>
              if hj : j < 1 then
                (kahanInputAbsMajorant fp v j (Nat.le_of_lt hj)).e
              else 0)
            steps +
            (kahanInputAbsMajorant fp v 1 (Nat.le_refl 1)).e ≤
          (C * (1 : ℝ) * fp.u ^ 2) *
            (∑ j : Fin steps.length, |(steps.get j).x|) := by
  rintro ⟨C, hC_nonneg, hall⟩
  let u : ℝ := 1 / (C + 1)
  have hden : 0 < C + 1 := by
    linarith
  have hu_pos : 0 < u := by
    dsimp [u]
    exact one_div_pos.mpr hden
  have hCu_le_one : C * u ≤ 1 := by
    dsimp [u]
    rw [mul_one_div, div_le_iff₀ hden]
    nlinarith
  have hineq := hall u hu_pos hCu_le_one
  exact
    not_kahanAffine_residualBudget_inputMajorant_one_of_Cu_le_one
      C u hu_pos hCu_le_one hineq

/-- Closed form for the biased small-unit-roundoff model on the two-term audit
input.  The returned-sum deviation is about `3u`, not `2u`, which is the formal
obstruction to proving the printed returned-Kahan coefficient theorem from the
bare `FPModel` axioms alone. -/
theorem fl_kahanSum_biasedSmallCounterexample_twoStep :
    fl_kahanSum
        (kahanBiasedSmallCounterexampleFPModel (1 / 1000) (by norm_num)) 2
        kahanBiasedTwoStepInput =
      (1003004003001 : ℝ) / 1000000000000 := by
  unfold fl_kahanSum fl_kahanState kahanPrefixState
  rw [Fin.foldl_succ_last]
  rw [Fin.foldl_succ_last]
  norm_num [kahanStep,
    kahanStepTrace, KahanStepTrace.nextState, KahanState.zero,
    kahanBiasedSmallCounterexampleFPModel, kahanBiasedTwoStepInput]

/-- Parametric closed form for the biased small-unit-roundoff model on the
two-term audit input.  For `0 < u < 1`, the unique returned coefficient has
first-order deviation `3*u`. -/
theorem fl_kahanSum_biasedSmallCounterexample_twoStep_of_pos_lt_one
    {u : ℝ} (hu : 0 ≤ u) (hu_pos : 0 < u) (hu_lt_one : u < 1) :
    fl_kahanSum (kahanBiasedSmallCounterexampleFPModel u hu) 2
        kahanBiasedTwoStepInput =
      1 + 3 * u + 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 := by
  have h_one_ne : (1 : ℝ) ≠ 0 := by norm_num
  have h_one_add_pos : 0 < 1 + u := by nlinarith
  have h_one_add_ne : 1 + u ≠ 0 := ne_of_gt h_one_add_pos
  have h_one_sub_pos : 0 < 1 - u := by nlinarith
  have h_one_sub_ne : 1 - u ≠ 0 := ne_of_gt h_one_sub_pos
  have h_neg_one_sub_ne : -1 - u ≠ 0 := by nlinarith
  have h_e_add_branch : ¬ (-1 - u = 0 ∨ 1 - u = 0) := by
    intro h
    rcases h with h | h
    · exact h_neg_one_sub_ne h
    · exact h_one_sub_ne h
  have h_e_add_branch' : ¬ (-u + -1 = 0 ∨ 1 - u = 0) := by
    intro h
    rcases h with h | h
    · have : -1 - u = 0 := by nlinarith
      exact h_neg_one_sub_ne this
    · exact h_one_sub_ne h
  have hsub_ne : (0 - (1 + u)) * (1 - u) ≠ 0 := by
    have hprod_pos : 0 < (1 + u) * (1 - u) :=
      mul_pos h_one_add_pos h_one_sub_pos
    nlinarith
  unfold fl_kahanSum fl_kahanState kahanPrefixState
  rw [Fin.foldl_succ_last]
  rw [Fin.foldl_succ_last]
  norm_num [kahanStep, kahanStepTrace, KahanStepTrace.nextState,
    KahanState.zero, kahanBiasedSmallCounterexampleFPModel,
    kahanBiasedTwoStepInput, h_one_ne, h_one_add_ne, hsub_ne,
    h_e_add_branch]
  rw [if_neg h_e_add_branch']
  ring_nf

/-- Generic version of the biased small-`u` returned-cap obstruction.

For any proposed second-order constant `C`, whenever `C*u <= 1/2`, the model's
returned value on `[1,0]` cannot be represented with all source weights bounded
by `2*u + C*u^2`.  This records the first-order obstruction independently of
the particular exact-subtraction constants used below. -/
theorem not_exists_fl_kahanSum_biasedSmallCounterexample_twoStep_source_bound_of_Cu_le_half
    {u C : ℝ} (hu : 0 ≤ u) (hu_pos : 0 < u) (hu_lt_one : u < 1)
    (hCu : C * u ≤ 1 / 2) :
    ¬ ∃ μ : Fin 2 → ℝ,
      (∀ i, |μ i| ≤ 2 * u + C * u ^ 2) ∧
      fl_kahanSum (kahanBiasedSmallCounterexampleFPModel u hu) 2
          kahanBiasedTwoStepInput =
        ∑ i : Fin 2, kahanBiasedTwoStepInput i * (1 + μ i) := by
  intro h
  rcases h with ⟨μ, hμ, hsum⟩
  have hsum_closed :
      fl_kahanSum (kahanBiasedSmallCounterexampleFPModel u hu) 2
        kahanBiasedTwoStepInput =
        1 + 3 * u + 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 :=
    fl_kahanSum_biasedSmallCounterexample_twoStep_of_pos_lt_one
      hu hu_pos hu_lt_one
  have hsource :
      (∑ i : Fin 2, kahanBiasedTwoStepInput i * (1 + μ i)) =
        1 + μ ⟨0, by decide⟩ := by
    norm_num [kahanBiasedTwoStepInput]
  have hmu_eq :
      μ ⟨0, by decide⟩ =
        3 * u + 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 := by
    nlinarith [hsum, hsum_closed, hsource]
  have hupper :
      μ ⟨0, by decide⟩ ≤ 2 * u + C * u ^ 2 :=
    (abs_le.mp (hμ ⟨0, by decide⟩)).2
  have hmu0 :
      μ 0 = 3 * u + 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 := by
    simpa using hmu_eq
  have hupper' :
      3 * u + 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 ≤
        2 * u + C * u ^ 2 := by
    simpa [hmu0] using hupper
  have hCu_sq : C * u ^ 2 ≤ (1 / 2) * u := by
    have hmul := mul_le_mul_of_nonneg_right hCu hu
    nlinarith
  have hpos_tail : 0 ≤ 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 := by
    have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
    have hu3 : 0 ≤ u ^ 3 := by nlinarith [hu, hu2]
    have hu4 : 0 ≤ u ^ 4 := by nlinarith [hu2]
    nlinarith
  nlinarith [hupper', hCu_sq, hpos_tail, hu_pos]

/-- For every nonnegative proposed second-order constant and every positive
unit-roundoff neighbourhood, there is a positive unit roundoff in that
neighbourhood for which C*u is at most one half.  This packages the
quantifier step needed to turn the parametric Kahan counterexample into a
genuine first-order source discrepancy. -/
theorem exists_kahanBiasedSmallCounterexample_unitRoundoff
    {C epsilon : Real} (hC : 0 <= C) (hepsilon : 0 < epsilon) :
    exists u : Real,
      0 <= u /\ 0 < u /\ u < 1 /\ u <= epsilon /\ C * u <= 1 / 2 := by
  let d : Real := 4 * (C + 1) * (epsilon + 1)
  have hC1 : 0 < C + 1 := by linarith
  have hepsilon1 : 0 < epsilon + 1 := by linarith
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hd_one : 1 <= d := by
    dsimp [d]
    nlinarith [mul_nonneg hC (le_of_lt hepsilon)]
  let u : Real := epsilon / d
  have hu_pos : 0 < u := by
    dsimp [u]
    exact div_pos hepsilon hd
  have hu : 0 <= u := le_of_lt hu_pos
  have hu_lt_one : u < 1 := by
    dsimp [u]
    rw [div_lt_one hd]
    dsimp [d]
    nlinarith [mul_nonneg hC (le_of_lt hepsilon)]
  have hu_le_epsilon : u <= epsilon := by
    dsimp [u]
    rw [div_le_iff₀ hd]
    have hmul :=
      mul_le_mul_of_nonneg_left hd_one (le_of_lt hepsilon)
    simpa using hmul
  have hCu : C * u <= 1 / 2 := by
    dsimp [u]
    rw [← mul_div_assoc]
    rw [div_le_iff₀ hd]
    dsimp [d]
    nlinarith [mul_nonneg hC (le_of_lt hepsilon)]
  exact ⟨u, hu, hu_pos, hu_lt_one, hu_le_epsilon, hCu⟩

/-- Uniform two-term formulation of the printed first-order content of
Higham (4.8) over the bare floating-point model.  A fixed C is allowed to
absorb the O(u^2) term, and the assertion is required only in a positive
neighbourhood of zero. -/
def Higham48BareFPModelTwoTermSecondOrderBound
    (C epsilon : Real) : Prop :=
  forall (fp : FPModel), 0 < fp.u -> fp.u <= epsilon ->
    exists mu : Fin 2 -> Real,
      (forall i, |mu i| <= 2 * fp.u + C * fp.u ^ 2) /\
      fl_kahanSum fp 2 kahanBiasedTwoStepInput =
        Finset.univ.sum
          (fun i : Fin 2 => kahanBiasedTwoStepInput i * (1 + mu i))

/-- Model-strength discrepancy terminal for Higham (4.8) in the repository's bare
floating-point model: even for n=2, no fixed second-order constant makes the
printed leading-2*u backward-error assertion true on any neighbourhood of
u=0.  The countermodels have arbitrarily small positive unit roundoff.

This result concerns only the abstract FPModel contract.  In particular, it
does not by itself refute the printed claim for correctly rounded finite
arithmetic, whose representable-result coherence excludes this family. -/
theorem not_exists_higham48BareFPModelTwoTermSecondOrderBound :
    Not (exists C epsilon : Real,
      0 <= C /\ 0 < epsilon /\
        Higham48BareFPModelTwoTermSecondOrderBound C epsilon) := by
  rintro ⟨C, epsilon, hC, hepsilon, hclaim⟩
  obtain ⟨u, hu, hu_pos, hu_lt_one, hu_le_epsilon, hCu⟩ :=
    exists_kahanBiasedSmallCounterexample_unitRoundoff hC hepsilon
  let fp := kahanBiasedSmallCounterexampleFPModel u hu
  have hfp_pos : 0 < fp.u := by
    simpa [fp, kahanBiasedSmallCounterexampleFPModel] using hu_pos
  have hfp_le : fp.u <= epsilon := by
    simpa [fp, kahanBiasedSmallCounterexampleFPModel] using hu_le_epsilon
  rcases hclaim fp hfp_pos hfp_le with ⟨mu, hmu, hsum⟩
  apply
    not_exists_fl_kahanSum_biasedSmallCounterexample_twoStep_source_bound_of_Cu_le_half
      hu hu_pos hu_lt_one hCu
  refine ⟨mu, ?_, ?_⟩
  · intro i
    simpa [fp, kahanBiasedSmallCounterexampleFPModel] using hmu i
  · simpa [fp] using hsum

/-- Pointwise forward-error obstruction corresponding to the biased Kahan
countermodel.  Its returned error has leading coefficient 3, so a proposed
leading-2 bound plus C*u^2 fails whenever C*u is at most one half. -/
theorem
    not_fl_kahanSum_biasedSmallCounterexample_twoStep_forward_bound_of_Cu_le_half
    {u C : Real} (hu : 0 <= u) (hu_pos : 0 < u) (hu_lt_one : u < 1)
    (hCu : C * u <= 1 / 2) :
    Not
      (|fl_kahanSum (kahanBiasedSmallCounterexampleFPModel u hu) 2
            kahanBiasedTwoStepInput -
          Finset.univ.sum (fun i : Fin 2 => kahanBiasedTwoStepInput i)| <=
        (2 * u + C * u ^ 2) *
          Finset.univ.sum (fun i : Fin 2 => |kahanBiasedTwoStepInput i|)) := by
  intro hbound
  have hsum_closed :
      fl_kahanSum (kahanBiasedSmallCounterexampleFPModel u hu) 2
          kahanBiasedTwoStepInput =
        1 + 3 * u + 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 :=
    fl_kahanSum_biasedSmallCounterexample_twoStep_of_pos_lt_one
      hu hu_pos hu_lt_one
  have hsum_exact :
      Finset.univ.sum (fun i : Fin 2 => kahanBiasedTwoStepInput i) = 1 := by
    norm_num [kahanBiasedTwoStepInput]
  have habs_exact :
      Finset.univ.sum (fun i : Fin 2 => |kahanBiasedTwoStepInput i|) = 1 := by
    norm_num [kahanBiasedTwoStepInput]
  rw [hsum_closed, hsum_exact, habs_exact, mul_one] at hbound
  have hu2 : 0 <= u ^ 2 := sq_nonneg u
  have hu3 : 0 <= u ^ 3 := by nlinarith [hu, hu2]
  have hu4 : 0 <= u ^ 4 := by nlinarith [hu2]
  have herror_nonneg :
      0 <= 3 * u + 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 := by
    nlinarith
  have herror :
      3 * u + 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 <=
        2 * u + C * u ^ 2 := by
    rw [show
      1 + 3 * u + 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 - 1 =
        3 * u + 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 by ring,
      abs_of_nonneg herror_nonneg] at hbound
    exact hbound
  have hCu_sq : C * u ^ 2 <= (1 / 2) * u := by
    have hmul := mul_le_mul_of_nonneg_right hCu hu
    nlinarith
  have htail : 0 <= 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 := by
    nlinarith
  nlinarith [herror, hCu_sq, htail, hu_pos]

/-- Uniform two-term formulation of the printed first-order content of
Higham (4.9) over the bare floating-point model. -/
def Higham49BareFPModelTwoTermSecondOrderBound
    (C epsilon : Real) : Prop :=
  forall (fp : FPModel), 0 < fp.u -> fp.u <= epsilon ->
    |fl_kahanSum fp 2 kahanBiasedTwoStepInput -
        Finset.univ.sum (fun i : Fin 2 => kahanBiasedTwoStepInput i)| <=
      (2 * fp.u + C * fp.u ^ 2) *
        Finset.univ.sum (fun i : Fin 2 => |kahanBiasedTwoStepInput i|)

/-- Model-strength discrepancy terminal for Higham (4.9) in the repository's bare
floating-point model: no fixed second-order constant repairs the printed
leading-2*u forward bound near u=0, already for the two-term input [1,0].

As above, this is a limitation theorem for FPModel, not a finite-format
counterexample to the source statement. -/
theorem not_exists_higham49BareFPModelTwoTermSecondOrderBound :
    Not (exists C epsilon : Real,
      0 <= C /\ 0 < epsilon /\
        Higham49BareFPModelTwoTermSecondOrderBound C epsilon) := by
  rintro ⟨C, epsilon, hC, hepsilon, hclaim⟩
  obtain ⟨u, hu, hu_pos, hu_lt_one, hu_le_epsilon, hCu⟩ :=
    exists_kahanBiasedSmallCounterexample_unitRoundoff hC hepsilon
  let fp := kahanBiasedSmallCounterexampleFPModel u hu
  have hfp_pos : 0 < fp.u := by
    simpa [fp, kahanBiasedSmallCounterexampleFPModel] using hu_pos
  have hfp_le : fp.u <= epsilon := by
    simpa [fp, kahanBiasedSmallCounterexampleFPModel] using hu_le_epsilon
  have hbound := hclaim fp hfp_pos hfp_le
  apply
    not_fl_kahanSum_biasedSmallCounterexample_twoStep_forward_bound_of_Cu_le_half
      hu hu_pos hu_lt_one hCu
  simpa [fp, kahanBiasedSmallCounterexampleFPModel] using hbound

/-- The small-unit-roundoff biased model rejects the common false shortcut
that the source-shaped returned-Kahan theorem follows from the bare `FPModel`
contract with the exact-subtraction-route constants.

For `u = 1/1000`, the returned value on `[1,0]` has the unique source
coefficient `1 + μ` with
`μ = 3u + 4u^2 + 3u^3 + u^4`, exceeding
`2u + 2*(3+40*2)*u^2`.  Thus the remaining Eq. (4.8) proof must use genuine
finite-format/coherence structure or a stronger coefficient argument; it cannot
be discharged by the abstract model and a loose second-order constant alone. -/
theorem not_forall_fl_kahanSum_backward_error_source_bound_bare_fpmodel_exactSubConstants :
    ¬ ∀ (fp : FPModel) (n : ℕ) (v : Fin n → ℝ),
      fp.u ≤ 1 / 64 →
      (3 + 40 * (n : ℝ)) * fp.u ≤ 1 →
      ∃ μ : Fin n → ℝ,
        (∀ i, |μ i| ≤
          2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
        fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  intro h
  let u : ℝ := 1 / 1000
  have hu : 0 ≤ u := by norm_num [u]
  let fp := kahanBiasedSmallCounterexampleFPModel u hu
  let v := kahanBiasedTwoStepInput
  have huSmall : fp.u ≤ 1 / 64 := by
    norm_num [fp, u, kahanBiasedSmallCounterexampleFPModel]
  have hBudget : (3 + 40 * (2 : ℝ)) * fp.u ≤ 1 := by
    norm_num [fp, u, kahanBiasedSmallCounterexampleFPModel]
  rcases h fp 2 v huSmall hBudget with ⟨μ, hμ, hsum⟩
  have hsum_closed :
      fl_kahanSum fp 2 v =
        (1003004003001 : ℝ) / 1000000000000 := by
    simpa [fp, v, u] using fl_kahanSum_biasedSmallCounterexample_twoStep
  have hsource :
      (∑ i : Fin 2, v i * (1 + μ i)) = 1 + μ ⟨0, by decide⟩ := by
    norm_num [v, kahanBiasedTwoStepInput]
  have hmu_eq :
      μ ⟨0, by decide⟩ = (3004003001 : ℝ) / 1000000000000 := by
    nlinarith [hsum, hsum_closed, hsource]
  have hbound' :
      μ ⟨0, by decide⟩ ≤
        2 * fp.u + 2 * (3 + 40 * (2 : ℝ)) * fp.u ^ 2 := by
    exact (abs_le.mp (hμ ⟨0, by decide⟩)).2
  have hmu0 : μ 0 = (3004003001 : ℝ) / 1000000000000 := by
    simpa using hmu_eq
  have hfalse :
      ((3004003001 : ℝ) / 1000000000000) ≤
        2 * fp.u + 2 * (3 + 40 * (2 : ℝ)) * fp.u ^ 2 := by
    simpa [hmu0] using hbound'
  norm_num [fp, u, kahanBiasedSmallCounterexampleFPModel] at hfalse

/-- Source-shaped backward-error bridge for the ordinary returned Kahan sum
from a supplied per-input returned-source coefficient bound.

This theorem deliberately keeps the coefficient bound as a hypothesis.  The
open Higham equation (4.8) work is exactly to prove that hypothesis with
`B = 2*u + O(n*u^2)` from the floating-point assumptions. -/
theorem fl_kahanSum_backward_error_source_bound_of_sourceCoeff_s_bound
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) {B : ℝ}
    (hcoeff :
      let steps := kahanCoupledCoeffSteps fp v n (Nat.le_refl n)
      ∀ i : Fin steps.length,
        |(kahanCoupledSourceCoeff steps i).s - 1| ≤ B) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ B) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  let steps := kahanCoupledCoeffSteps fp v n (Nat.le_refl n)
  have hcoeff' :
      ∀ i : Fin steps.length,
        |(kahanCoupledSourceCoeff steps i).s - 1| ≤ B := by
    simpa [steps] using hcoeff
  have hlen : n = steps.length := by
    simp [steps, kahanCoupledCoeffSteps]
  let idx : Fin n → Fin steps.length := fun i => finCongr hlen i
  let μ : Fin n → ℝ := fun i => (kahanCoupledSourceCoeff steps (idx i)).s - 1
  refine ⟨μ, ?_, ?_⟩
  · intro i
    dsimp [μ]
    exact hcoeff' (idx i)
  · have hs :=
      kahanCoupledCoeffSteps_prefixState_s_eq_sum_sourceCoeff
        fp v n (Nat.le_refl n)
    have hsum :
        (∑ i : Fin n, v i * (1 + μ i)) =
          ∑ j : Fin steps.length,
            (steps.get j).x * (kahanCoupledSourceCoeff steps j).s := by
      refine Fintype.sum_equiv (finCongr hlen) _ _ ?_
      intro i
      dsimp [μ, idx]
      simp [steps, kahanCoupledCoeffSteps, kahanCoupledCoeffStepOfIndex]
    simpa [fl_kahanSum, fl_kahanState, steps] using hs.trans hsum.symm

/-- Source-shaped backward-error bridge for the ordinary returned Kahan sum
from explicit witness-family source coefficient bounds.

This is the witness-parametric companion of
`fl_kahanSum_backward_error_source_bound_of_sourceCoeff_s_bound`; it is the
right surface for the exact-subtraction route because the witness family can
be chosen constructively from finite-format/coherence hypotheses. -/
theorem fl_kahanSum_backward_error_source_bound_of_witnessSourceCoeff_s_bound
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (W : KahanPrefixDeltaWitnessFamily fp v n (Nat.le_refl n)) {B : ℝ}
    (hcoeff :
      let steps := kahanCoupledCoeffStepsOfWitnesses fp v n (Nat.le_refl n) W
      ∀ i : Fin steps.length,
        |(kahanCoupledSourceCoeff steps i).s - 1| ≤ B) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ B) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  let steps := kahanCoupledCoeffStepsOfWitnesses fp v n (Nat.le_refl n) W
  have hcoeff' :
      ∀ i : Fin steps.length,
        |(kahanCoupledSourceCoeff steps i).s - 1| ≤ B := by
    simpa [steps] using hcoeff
  have hlen : n = steps.length := by
    simp [steps, kahanCoupledCoeffStepsOfWitnesses]
  let idx : Fin n → Fin steps.length := fun i => finCongr hlen i
  let μ : Fin n → ℝ := fun i => (kahanCoupledSourceCoeff steps (idx i)).s - 1
  refine ⟨μ, ?_, ?_⟩
  · intro i
    dsimp [μ]
    exact hcoeff' (idx i)
  · have hs :=
      kahanCoupledCoeffStepsOfWitnesses_prefixState_s_eq_sum_sourceCoeff
        fp v n (Nat.le_refl n) W
    have hsum :
        (∑ i : Fin n, v i * (1 + μ i)) =
          ∑ j : Fin steps.length,
            (steps.get j).x * (kahanCoupledSourceCoeff steps j).s := by
      refine Fintype.sum_equiv (finCongr hlen) _ _ ?_
      intro i
      dsimp [μ, idx]
      simp [steps, kahanCoupledCoeffStepsOfWitnesses,
        kahanCoupledCoeffStepOfWitness]
    simpa [fl_kahanSum, fl_kahanState, steps] using hs.trans hsum.symm

/-- Conditional source-shaped backward-error representation for the ordinary
returned Kahan sum along an explicit exact-subtraction witness-family route.

This is the Eq. (4.8)-shaped formal surface still missing from the arbitrary
chosen-witness route: the only remaining finite-format obligation is to
construct a witness family satisfying `deltaSub = 0` at each correction
subtraction. -/
theorem fl_kahanSum_backward_error_source_bound_of_exactSubWitnesses
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (W : KahanPrefixDeltaWitnessFamily fp v n (Nat.le_refl n))
    (huSmall : fp.u ≤ 1 / 64)
    (hExactSub :
      kahanCoupledCoeffStepsOfWitnessesExactSub fp v n (Nat.le_refl n) W)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  let steps := kahanCoupledCoeffStepsOfWitnesses fp v n (Nat.le_refl n) W
  refine
    fl_kahanSum_backward_error_source_bound_of_witnessSourceCoeff_s_bound
      fp n v W ?_
  dsimp
  intro j
  have hdrop_nat :
      (steps.drop (j.val + 1)).length ≤ steps.length := by
    rw [List.length_drop]
    exact Nat.sub_le steps.length (j.val + 1)
  have hlen : n = steps.length := by
    simp [steps, kahanCoupledCoeffStepsOfWitnesses]
  have hdrop_le :
      ((steps.drop (j.val + 1)).length : ℝ) ≤ (n : ℝ) := by
    have hdrop_le_steps :
        ((steps.drop (j.val + 1)).length : ℝ) ≤
          (steps.length : ℝ) := by
      exact_mod_cast hdrop_nat
    simp [hlen] at hdrop_le_steps ⊢
  have hbudget_j :
      (3 + 40 * ((steps.drop (j.val + 1)).length : ℝ)) *
          fp.u ≤ 1 := by
    have hcoef :
        3 + 40 * ((steps.drop (j.val + 1)).length : ℝ) ≤
          3 + 40 * (n : ℝ) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcoef fp.u_nonneg
    nlinarith
  have hcoeff :=
    kahanCoupledCoeffStepsOfWitnesses_sourceCoeff_s_abs_sub_one_le_two_u_plus_exactSubMajorant
      fp v n (Nat.le_refl n) W huSmall hExactSub j
      (by simpa [steps] using hbudget_j)
  have htarget :
      |(kahanCoupledSourceCoeff steps j).s - 1| ≤
        2 * fp.u +
          2 * (3 + 40 * ((steps.drop (j.val + 1)).length : ℝ)) *
            fp.u ^ 2 := by
    simpa [steps] using hcoeff
  have hcoef2 :
      2 * (3 + 40 * ((steps.drop (j.val + 1)).length : ℝ)) *
          fp.u ^ 2 ≤
        2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2 := by
    have hcoef :
        3 + 40 * ((steps.drop (j.val + 1)).length : ℝ) ≤
          3 + 40 * (n : ℝ) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg fp.u)
    nlinarith
  nlinarith

/-- Conditional source-shaped backward-error representation for the ordinary
returned Kahan sum from exact correction subtraction in the actual prefix
trace.

This composes the operation-level exact-subtraction surface with the explicit
witness-family route, so callers no longer need to manipulate roundoff
witnesses directly.  The remaining finite-format work is to prove
`KahanPrefixCorrectionSubExact` from concrete correction-formula/coherence
hypotheses. -/
theorem fl_kahanSum_backward_error_source_bound_of_exactSubTrace
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hExactSubTrace :
      KahanPrefixCorrectionSubExact fp v n (Nat.le_refl n))
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  let W :=
    kahanPrefixDeltaWitnessFamilyOfExactSub
      fp v n (Nat.le_refl n) hExactSubTrace
  have hW :
      kahanCoupledCoeffStepsOfWitnessesExactSub
        fp v n (Nat.le_refl n) W := by
    simpa [W] using
      kahanPrefixDeltaWitnessFamilyOfExactSub_exactSub
        fp v n (Nat.le_refl n) hExactSubTrace
  exact
    fl_kahanSum_backward_error_source_bound_of_exactSubWitnesses
      fp n v W huSmall hW hBudget

/-- Conditional source-shaped backward-error representation for the ordinary
returned Kahan sum from finite representability of every displayed correction
subtraction in a concrete finite round-to-even format.

This is the finite/coherence layer below the FastTwoSum route: callers may
prove `FiniteKahanPrefixCorrectionSubFinite` directly, for example from
Sterbenz or Ferguson conditions on `temp - s`, without using a magnitude-order
FastTwoSum certificate. -/
theorem fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sub_finite
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (n : ℕ) (v : Fin n → ℝ)
    (hfinite :
      FiniteKahanPrefixCorrectionSubFinite fmt v n (Nat.le_refl n))
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_kahanSum_backward_error_source_bound_of_exactSubTrace
      fp n v
      (KahanPrefixCorrectionSubExact.of_finiteRoundToEven_sub_finite
        fp fmt hround v n (Nat.le_refl n) hfinite)
      huSmall hBudget

/-- Tail-direct finite-subtraction route for the ordinary returned Kahan
backward-error representation.

The initialized first correction subtraction is finite because `temp = 0`, so
callers may supply finite representability only for the nonzero prefix
indices. -/
theorem fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sub_finite
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (n : ℕ) (v : Fin n → ℝ)
    (hfiniteTail :
      ∀ i : Fin n, i.val ≠ 0 →
        fmt.finiteSystem
          ((finiteKahanTrace fmt v i).temp -
            (finiteKahanTrace fmt v i).s))
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sub_finite
      fp fmt hround n v
      (FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_sub_finite
        fmt v n (Nat.le_refl n)
        (fun i hi => by simpa using hfiniteTail i hi))
      huSmall hBudget

/-- Sterbenz-ratio finite/coherence route for the ordinary returned Kahan
backward-error representation. -/
theorem fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sterbenzLe
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (n : ℕ) (v : Fin n → ℝ)
    (hsterbenz :
      ∀ i : Fin n,
        fmt.sterbenzRatioConditionLe
          (finiteKahanTrace fmt v i).temp
          (finiteKahanTrace fmt v i).s)
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sub_finite
      fp fmt hround n v
      (FiniteKahanPrefixCorrectionSubFinite.of_sterbenzRatioConditionLe
        fmt v n (Nat.le_refl n) (fun i => by simpa using hsterbenz i))
      huSmall hBudget

/-- Ferguson-exponent finite/coherence route for the ordinary returned Kahan
backward-error representation. -/
theorem fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fergusonLe
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (n : ℕ) (v : Fin n → ℝ)
    (hferguson :
      ∀ i : Fin n,
        fmt.fergusonExponentConditionLe
          (finiteKahanTrace fmt v i).temp
          (finiteKahanTrace fmt v i).s)
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sub_finite
      fp fmt hround n v
      (FiniteKahanPrefixCorrectionSubFinite.of_fergusonConditionLe
        fmt v n (Nat.le_refl n) (fun i => by simpa using hferguson i))
      huSmall hBudget

/-- Tail-only Sterbenz finite/coherence route for the ordinary returned Kahan
backward-error representation.

The initialized first correction subtraction has `temp = 0`, hence is finite
from the rounded trace itself; only indices with nonzero prefix position need
the Sterbenz condition. -/
theorem fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sterbenzLe
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (n : ℕ) (v : Fin n → ℝ)
    (hsterbenz :
      ∀ i : Fin n, i.val ≠ 0 →
        fmt.sterbenzRatioConditionLe
          (finiteKahanTrace fmt v i).temp
          (finiteKahanTrace fmt v i).s)
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sub_finite
      fp fmt hround n v
      (FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_sterbenzLe
        fmt v n (Nat.le_refl n)
        (fun i hi => by simpa using hsterbenz i hi))
      huSmall hBudget

/-- Tail-only Ferguson finite/coherence route for the ordinary returned Kahan
backward-error representation.

As in the Sterbenz tail route, the first correction subtraction is finite
because `temp = 0`; the Ferguson condition is required only on subsequent
trace steps. -/
theorem fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_fergusonLe
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (n : ℕ) (v : Fin n → ℝ)
    (hferguson :
      ∀ i : Fin n, i.val ≠ 0 →
        fmt.fergusonExponentConditionLe
          (finiteKahanTrace fmt v i).temp
          (finiteKahanTrace fmt v i).s)
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sub_finite
      fp fmt hround n v
      (FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_fergusonLe
        fmt v n (Nat.le_refl n)
        (fun i hi => by simpa using hferguson i hi))
      huSmall hBudget

/-- Conditional source-shaped backward-error representation for the ordinary
returned Kahan sum from concrete finite-format FastTwoSum certificates.

This is the finite-format bridge for Higham equation (4.8): once the abstract
model is identified with the finite round-to-even add/sub operations and each
Kahan correction-formula step supplies the FastTwoSum representability
certificate, the exact-subtraction witness route applies end-to-end. -/
theorem fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fastTwoSumCertificates
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (n : ℕ) (v : Fin n → ℝ)
    (hcerts :
      KahanPrefixFastTwoSumFiniteCertificates fmt v n (Nat.le_refl n))
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_kahanSum_backward_error_source_bound_of_exactSubTrace
      fp n v
      (KahanPrefixCorrectionSubExact.of_finiteRoundToEven_fastTwoSumCertificates
        fp fmt hround v n (Nat.le_refl n) hcerts)
      huSmall hBudget

/-- Conditional source-shaped backward-error representation for the ordinary
returned Kahan sum from the base-2 absolute-order FastTwoSum hypotheses at
each finite-format Kahan correction step. -/
theorem fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_abs_gt
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (n : ℕ) (v : Fin n → ℝ)
    (hfiniteTemp :
      ∀ i : Fin n, fmt.finiteSystem (finiteKahanTrace fmt v i).temp)
    (hfiniteY :
      ∀ i : Fin n, fmt.finiteSystem (finiteKahanTrace fmt v i).y)
    (horder :
      ∀ i : Fin n,
        |(finiteKahanTrace fmt v i).y| <
          |(finiteKahanTrace fmt v i).temp|)
    (hrange :
      ∀ i : Fin n,
        fmt.finiteNormalRange
          ((finiteKahanTrace fmt v i).temp +
            (finiteKahanTrace fmt v i).y))
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  have hcerts :
      KahanPrefixFastTwoSumFiniteCertificates
        fmt v n (Nat.le_refl n) := by
    exact
      KahanPrefixFastTwoSumFiniteCertificates.of_base2_abs_gt
        fmt hbeta ht v n (Nat.le_refl n)
        (fun i => by simpa using hfiniteTemp i)
        (fun i => by simpa using hfiniteY i)
        (fun i => by simpa using horder i)
        (fun i => by simpa using hrange i)
  exact
    fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fastTwoSumCertificates
      fp fmt hround n v hcerts huSmall hBudget

/-- Conditional source-shaped backward-error representation for the ordinary
returned Kahan sum from the two remaining base-2 correction-formula
obligations at each finite-format Kahan step: magnitude order and normal
range.  Finiteness of `temp` and `y` is supplied by the finite trace itself. -/
theorem fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_abs_gt_of_order_range
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (n : ℕ) (v : Fin n → ℝ)
    (horder :
      ∀ i : Fin n,
        |(finiteKahanTrace fmt v i).y| <
          |(finiteKahanTrace fmt v i).temp|)
    (hrange :
      ∀ i : Fin n,
        fmt.finiteNormalRange
          ((finiteKahanTrace fmt v i).temp +
            (finiteKahanTrace fmt v i).y))
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_abs_gt
      fp fmt hround hbeta ht n v
      (finiteKahanTrace_temp_finiteSystem fmt v)
      (finiteKahanTrace_y_finiteSystem fmt v)
      horder hrange huSmall hBudget

/-- Conditional source-shaped backward-error representation for the ordinary
returned Kahan sum from tail-only base-2 correction-formula obligations.

The first correction-formula step starts with `temp = 0`, so it is closed by
finite zero-add exactness.  Only the later steps need the usual FastTwoSum
magnitude-order and normal-range hypotheses. -/
theorem fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_tail_order_range
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (n : ℕ) (v : Fin n → ℝ)
    (horder :
      ∀ i : Fin n, i.val ≠ 0 →
        |(finiteKahanTrace fmt v i).y| <
          |(finiteKahanTrace fmt v i).temp|)
    (hrange :
      ∀ i : Fin n, i.val ≠ 0 →
        fmt.finiteNormalRange
          ((finiteKahanTrace fmt v i).temp +
            (finiteKahanTrace fmt v i).y))
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  have hcerts :
      KahanPrefixFastTwoSumFiniteCertificates
        fmt v n (Nat.le_refl n) := by
    exact
      KahanPrefixFastTwoSumFiniteCertificates.of_first_exact_and_tail_base2_abs_gt
        fmt hbeta ht v n (Nat.le_refl n)
        (fun i hi => by simpa using horder i hi)
        (fun i hi => by simpa using hrange i hi)
  exact
    fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fastTwoSumCertificates
      fp fmt hround n v hcerts huSmall hBudget

/-- First input in the four-term finite round-to-even returned-Kahan
counterexample obtained from the strict Chapter 4 follow-up. -/
noncomputable def highamCh4KahanReturnedCounterexampleX1 : Real := -22

/-- Second input in the four-term finite round-to-even returned-Kahan
counterexample.  The parameter `p` is `2^precision`; for the concrete p=5
format below this is `32`. -/
noncomputable def highamCh4KahanReturnedCounterexampleX2 (p : Real) : Real :=
  -(2 * p + 4)

/-- Third input in the four-term finite round-to-even returned-Kahan
counterexample. -/
noncomputable def highamCh4KahanReturnedCounterexampleX3 (p : Real) : Real :=
  -(8 * p - 8)

/-- Fourth input in the four-term finite round-to-even returned-Kahan
counterexample. -/
noncomputable def highamCh4KahanReturnedCounterexampleX4 : Real := 8

/-- Stored sum after the second finite Kahan step in the counterexample trace. -/
noncomputable def highamCh4KahanReturnedCounterexampleS2 (p : Real) : Real :=
  -(2 * p + 24)

/-- Rounded `y` value in the third finite Kahan step of the counterexample
trace. -/
noncomputable def highamCh4KahanReturnedCounterexampleY3 (p : Real) : Real :=
  -(8 * p)

/-- Final stored sum in the four-term finite round-to-even returned-Kahan
counterexample trace. -/
noncomputable def highamCh4KahanReturnedCounterexampleS3 (p : Real) : Real :=
  -(10 * p + 32)

/-- Coefficient functions used to test source-weight backward-error
representations for the four-term returned-Kahan counterexample. -/
abbrev HighamCh4KahanReturnedCounterexampleWeight := Fin 4 -> Real

/-- Uniform bound on a source-weight coefficient function. -/
def highamCh4KahanReturnedCounterexampleMuBound
    (b : Real) (mu : Fin 4 -> Real) : Prop :=
  forall i, |mu i| <= b

/-- Four-term input vector for the finite round-to-even returned-Kahan
counterexample. -/
noncomputable def highamCh4KahanReturnedCounterexampleInput
    (p : Real) : Fin 4 -> Real :=
  fun i =>
    if i.val = 0 then highamCh4KahanReturnedCounterexampleX1
    else if i.val = 1 then highamCh4KahanReturnedCounterexampleX2 p
    else if i.val = 2 then highamCh4KahanReturnedCounterexampleX3 p
    else highamCh4KahanReturnedCounterexampleX4

/-- Source-weight representation predicate for the four-term returned-Kahan
counterexample. -/
def highamCh4KahanReturnedCounterexampleSourceRepresentation
    (fmt : FloatingPointFormat) (p b : Real) (mu : Fin 4 -> Real) : Prop :=
  And (highamCh4KahanReturnedCounterexampleMuBound b mu)
    (finiteKahanSum fmt 4 (highamCh4KahanReturnedCounterexampleInput p) =
      Finset.univ.sum (fun i : Fin 4 =>
        highamCh4KahanReturnedCounterexampleInput p i * (1 + mu i)))

/-- Concrete p=5 binary format used by the four-term returned-Kahan
counterexample.  Its normalized values have mantissas `16 <= m < 32` and
exponents `3 <= e <= 9`, so the local spacing around the counterexample
values is exactly the one used in the GPT-5.5 Pro trace. -/
def highamCh4KahanReturnedCounterexampleP5Format : FloatingPointFormat where
  beta := 2
  t := 5
  emin := 3
  emax := 9
  beta_ge_two := by norm_num
  t_pos := by norm_num
  emin_le_emax := by norm_num

theorem highamCh4KahanReturnedCounterexampleP5_finiteSystem_of_normalizedValue
    (negative : Bool) (m : Nat) (e : Int)
    (hm :
      highamCh4KahanReturnedCounterexampleP5Format.normalizedMantissa m)
    (he :
      highamCh4KahanReturnedCounterexampleP5Format.exponentInRange e) :
    highamCh4KahanReturnedCounterexampleP5Format.finiteSystem
      (highamCh4KahanReturnedCounterexampleP5Format.normalizedValue
        negative m e) := by
  right
  left
  refine Exists.intro negative ?_
  refine Exists.intro m ?_
  refine Exists.intro e ?_
  exact And.intro hm (And.intro he rfl)

theorem highamCh4KahanReturnedCounterexampleP5_finiteSystem_neg22 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteSystem
      (-22 : Real) := by
  have h :=
    highamCh4KahanReturnedCounterexampleP5_finiteSystem_of_normalizedValue
      true 22 (5 : Int)
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa,
          FloatingPointFormat.maxNormalMantissa])
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.exponentInRange])
  convert h using 1
  norm_num [highamCh4KahanReturnedCounterexampleP5Format,
    FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
    FloatingPointFormat.betaR]

theorem highamCh4KahanReturnedCounterexampleP5_finiteSystem_pos22 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteSystem
      (22 : Real) := by
  have h :=
    highamCh4KahanReturnedCounterexampleP5_finiteSystem_of_normalizedValue
      false 22 (5 : Int)
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa,
          FloatingPointFormat.maxNormalMantissa])
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.exponentInRange])
  convert h using 1
  norm_num [highamCh4KahanReturnedCounterexampleP5Format,
    FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
    FloatingPointFormat.betaR]

theorem highamCh4KahanReturnedCounterexampleP5_finiteSystem_neg68 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteSystem
      (-68 : Real) := by
  have h :=
    highamCh4KahanReturnedCounterexampleP5_finiteSystem_of_normalizedValue
      true 17 (7 : Int)
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa,
          FloatingPointFormat.maxNormalMantissa])
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.exponentInRange])
  convert h using 1
  norm_num [highamCh4KahanReturnedCounterexampleP5Format,
    FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
    FloatingPointFormat.betaR]

theorem highamCh4KahanReturnedCounterexampleP5_finiteSystem_neg4 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteSystem
      (-4 : Real) := by
  have h :=
    highamCh4KahanReturnedCounterexampleP5_finiteSystem_of_normalizedValue
      true 16 (3 : Int)
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa,
          FloatingPointFormat.maxNormalMantissa])
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.exponentInRange])
  convert h using 1
  norm_num [highamCh4KahanReturnedCounterexampleP5Format,
    FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
    FloatingPointFormat.betaR, zpow_neg]

theorem highamCh4KahanReturnedCounterexampleP5_finiteSystem_zero :
    highamCh4KahanReturnedCounterexampleP5Format.finiteSystem
      (0 : Real) := by
  exact Or.inl rfl

theorem highamCh4KahanReturnedCounterexampleP5_finiteSystem_pos8 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteSystem
      (8 : Real) := by
  have h :=
    highamCh4KahanReturnedCounterexampleP5_finiteSystem_of_normalizedValue
      false 16 (4 : Int)
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa,
          FloatingPointFormat.maxNormalMantissa])
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.exponentInRange])
  convert h using 1
  norm_num [highamCh4KahanReturnedCounterexampleP5Format,
    FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
    FloatingPointFormat.betaR, zpow_neg]
  rfl

theorem highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
    {op : BasicOp} {x y z : Real}
    (hz : BasicOp.exact op x y = z)
    (hfin :
      highamCh4KahanReturnedCounterexampleP5Format.finiteSystem z) :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
      op x y = z := by
  have hfin' :
      highamCh4KahanReturnedCounterexampleP5Format.finiteSystem
        (BasicOp.exact op x y) := by
    simpa [hz] using hfin
  simpa [hz] using
    (highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := op) (x := x) (y := y) hfin'
      )

theorem highamCh4KahanReturnedCounterexampleP5_sameExponentTie_left_even
    {x left right : Real} {m : Nat} {e : Int}
    (hm :
      highamCh4KahanReturnedCounterexampleP5Format.normalizedMantissa m)
    (hm1 :
      highamCh4KahanReturnedCounterexampleP5Format.normalizedMantissa
        (m + 1))
    (hleft :
      left =
        highamCh4KahanReturnedCounterexampleP5Format.normalizedValue
          false m e)
    (hright :
      right =
        highamCh4KahanReturnedCounterexampleP5Format.normalizedValue
          false (m + 1) e)
    (hrange :
      highamCh4KahanReturnedCounterexampleP5Format.finiteNormalRange x)
    (hstrict : And (left < x) (x < right))
    (htie : |x - left| = |x - right|)
    (heven : FloatingPointFormat.evenMantissa m) :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven x =
      left := by
  let fmt := highamCh4KahanReturnedCounterexampleP5Format
  have hstruct : fmt.sameExponentAdjacentNormalized left right := by
    refine Exists.intro false ?_
    refine Exists.intro m ?_
    refine Exists.intro e ?_
    exact And.intro hm (And.intro hm1 (Or.inl (And.intro hleft hright)))
  have hadj : fmt.realOrderAdjacentNormalized left right :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hrange
  exact
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
      hpolicy hadj hstrict hm hleft htie heven

theorem highamCh4KahanReturnedCounterexampleP5_sameExponentTie_right_odd
    {x left right : Real} {m : Nat} {e : Int}
    (hm :
      highamCh4KahanReturnedCounterexampleP5Format.normalizedMantissa m)
    (hm1 :
      highamCh4KahanReturnedCounterexampleP5Format.normalizedMantissa
        (m + 1))
    (hleft :
      left =
        highamCh4KahanReturnedCounterexampleP5Format.normalizedValue
          false m e)
    (hright :
      right =
        highamCh4KahanReturnedCounterexampleP5Format.normalizedValue
          false (m + 1) e)
    (hrange :
      highamCh4KahanReturnedCounterexampleP5Format.finiteNormalRange x)
    (hstrict : And (left < x) (x < right))
    (htie : |x - left| = |x - right|)
    (hodd : ¬ FloatingPointFormat.evenMantissa m) :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven x =
      right := by
  let fmt := highamCh4KahanReturnedCounterexampleP5Format
  have hstruct : fmt.sameExponentAdjacentNormalized left right := by
    refine Exists.intro false ?_
    refine Exists.intro m ?_
    refine Exists.intro e ?_
    exact And.intro hm (And.intro hm1 (Or.inl (And.intro hleft hright)))
  have hadj : fmt.realOrderAdjacentNormalized left right :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hrange
  exact
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hm hleft htie hodd

theorem highamCh4KahanReturnedCounterexampleP5_boundaryTie_right_odd
    {x left right : Real} {e : Int}
    (hleft :
      left =
        highamCh4KahanReturnedCounterexampleP5Format.normalizedValue
          false
          highamCh4KahanReturnedCounterexampleP5Format.maxNormalMantissa e)
    (hright :
      right =
        highamCh4KahanReturnedCounterexampleP5Format.normalizedValue
          false
          highamCh4KahanReturnedCounterexampleP5Format.minNormalMantissa
          (e + 1))
    (hrange :
      highamCh4KahanReturnedCounterexampleP5Format.finiteNormalRange x)
    (hstrict : And (left < x) (x < right))
    (htie : |x - left| = |x - right|)
    (hodd :
      ¬ FloatingPointFormat.evenMantissa
        highamCh4KahanReturnedCounterexampleP5Format.maxNormalMantissa) :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven x =
      right := by
  let fmt := highamCh4KahanReturnedCounterexampleP5Format
  have hm : fmt.normalizedMantissa fmt.maxNormalMantissa :=
    fmt.maxNormalMantissa_normalized
  have hboundary : fmt.boundaryAdjacentNormalized left right := by
    exact Exists.intro false
      (Exists.intro e (Or.inl (And.intro hleft hright)))
  have hadj : fmt.realOrderAdjacentNormalized left right :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hrange
  exact
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hm hleft htie hodd

theorem highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_90 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
      (90 : Real) = 88 := by
  apply highamCh4KahanReturnedCounterexampleP5_sameExponentTie_left_even
    (m := 22) (e := (7 : Int)) (left := 88) (right := 92)
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
  · rw [FloatingPointFormat.finiteNormalRange]
    norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.minNormalMagnitude,
      FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR]
    change (90 : Real) <= 496
    norm_num
  · norm_num
  · norm_num
  · norm_num [FloatingPointFormat.evenMantissa]

theorem highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_66 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
      (66 : Real) = 64 := by
  apply highamCh4KahanReturnedCounterexampleP5_sameExponentTie_left_even
    (m := 16) (e := (7 : Int)) (left := 64) (right := 68)
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
  · rw [FloatingPointFormat.finiteNormalRange]
    norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.minNormalMagnitude,
      FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR]
    change (66 : Real) <= 496
    norm_num
  · norm_num
  · norm_num
  · norm_num [FloatingPointFormat.evenMantissa]

theorem highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_252 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
      (252 : Real) = 256 := by
  apply highamCh4KahanReturnedCounterexampleP5_boundaryTie_right_odd
    (e := (8 : Int)) (left := 248) (right := 256)
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.minNormalMantissa]
  · rw [FloatingPointFormat.finiteNormalRange]
    norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.minNormalMagnitude,
      FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR]
    change (252 : Real) <= 496
    norm_num
  · norm_num
  · norm_num
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.evenMantissa]

theorem highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_264 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
      (264 : Real) = 256 := by
  apply highamCh4KahanReturnedCounterexampleP5_sameExponentTie_left_even
    (m := 16) (e := (9 : Int)) (left := 256) (right := 272)
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
  · rw [FloatingPointFormat.finiteNormalRange]
    norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.minNormalMagnitude,
      FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR]
    change (264 : Real) <= 496
    norm_num
  · norm_num
  · norm_num
  · norm_num [FloatingPointFormat.evenMantissa]

theorem highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_344 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
      (344 : Real) = 352 := by
  apply highamCh4KahanReturnedCounterexampleP5_sameExponentTie_right_odd
    (m := 21) (e := (9 : Int)) (left := 336) (right := 352)
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
  · rw [FloatingPointFormat.finiteNormalRange]
    norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.minNormalMagnitude,
      FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR]
    change (344 : Real) <= 496
    norm_num
  · norm_num
  · norm_num
  · norm_num [FloatingPointFormat.evenMantissa]

theorem highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_neg90 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
      (-90 : Real) = -88 := by
  have h :=
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven_neg
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.evenMantissa])
      (by norm_num [highamCh4KahanReturnedCounterexampleP5Format])
      (90 : Real)
  simpa [highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_90]
    using h

theorem highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_neg252 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
      (-252 : Real) = -256 := by
  have h :=
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven_neg
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.evenMantissa])
      (by norm_num [highamCh4KahanReturnedCounterexampleP5Format])
      (252 : Real)
  simpa [highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_252]
    using h

theorem highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_neg344 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
      (-344 : Real) = -352 := by
  have h :=
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven_neg
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.evenMantissa])
      (by norm_num [highamCh4KahanReturnedCounterexampleP5Format])
      (344 : Real)
  simpa [highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_344]
    using h

/-- Exact finite round-to-even identities for the four-term returned-Kahan
counterexample trace.

This isolates the remaining concrete finite-format proof obligation from the
algorithmic obstruction: once these identities are supplied by a p=5 binary
format, the theorem below shows the returned sum cannot satisfy a first-order
`2u` source coefficient cap. -/
structure HighamCh4KahanReturnedCounterexampleRounding
    (fmt : FloatingPointFormat) (p : Real) : Prop where
  y1 :
    fmt.finiteRoundToEvenOp BasicOp.add
      highamCh4KahanReturnedCounterexampleX1 0 =
    highamCh4KahanReturnedCounterexampleX1
  s1 :
    fmt.finiteRoundToEvenOp BasicOp.add 0
      highamCh4KahanReturnedCounterexampleX1 =
    highamCh4KahanReturnedCounterexampleX1
  q1 :
    fmt.finiteRoundToEvenOp BasicOp.sub 0
      highamCh4KahanReturnedCounterexampleX1 = 22
  e1 :
    fmt.finiteRoundToEvenOp BasicOp.add 22
      highamCh4KahanReturnedCounterexampleX1 = 0
  y2 :
    fmt.finiteRoundToEvenOp BasicOp.add
      (highamCh4KahanReturnedCounterexampleX2 p) 0 =
    highamCh4KahanReturnedCounterexampleX2 p
  s2 :
    fmt.finiteRoundToEvenOp BasicOp.add
      highamCh4KahanReturnedCounterexampleX1
      (highamCh4KahanReturnedCounterexampleX2 p) =
    highamCh4KahanReturnedCounterexampleS2 p
  q2 :
    fmt.finiteRoundToEvenOp BasicOp.sub
      highamCh4KahanReturnedCounterexampleX1
      (highamCh4KahanReturnedCounterexampleS2 p) = 2 * p
  e2 :
    fmt.finiteRoundToEvenOp BasicOp.add (2 * p)
      (highamCh4KahanReturnedCounterexampleX2 p) = -4
  y3 :
    fmt.finiteRoundToEvenOp BasicOp.add
      (highamCh4KahanReturnedCounterexampleX3 p) (-4) =
    highamCh4KahanReturnedCounterexampleY3 p
  s3 :
    fmt.finiteRoundToEvenOp BasicOp.add
      (highamCh4KahanReturnedCounterexampleS2 p)
      (highamCh4KahanReturnedCounterexampleY3 p) =
    highamCh4KahanReturnedCounterexampleS3 p
  q3 :
    fmt.finiteRoundToEvenOp BasicOp.sub
      (highamCh4KahanReturnedCounterexampleS2 p)
      (highamCh4KahanReturnedCounterexampleS3 p) = 8 * p
  e3 :
    fmt.finiteRoundToEvenOp BasicOp.add (8 * p)
      (highamCh4KahanReturnedCounterexampleY3 p) = 0
  y4 :
    fmt.finiteRoundToEvenOp BasicOp.add
      highamCh4KahanReturnedCounterexampleX4 0 =
    highamCh4KahanReturnedCounterexampleX4
  s4 :
    fmt.finiteRoundToEvenOp BasicOp.add
      (highamCh4KahanReturnedCounterexampleS3 p)
      highamCh4KahanReturnedCounterexampleX4 =
    highamCh4KahanReturnedCounterexampleS3 p
  q4 :
    fmt.finiteRoundToEvenOp BasicOp.sub
      (highamCh4KahanReturnedCounterexampleS3 p)
      (highamCh4KahanReturnedCounterexampleS3 p) = 0
  e4 :
    fmt.finiteRoundToEvenOp BasicOp.add 0
      highamCh4KahanReturnedCounterexampleX4 =
    highamCh4KahanReturnedCounterexampleX4

/-- The concrete p=5 binary format satisfies all finite round-to-even trace
identities for the four-term returned-Kahan obstruction. -/
theorem highamCh4KahanReturnedCounterexampleP5_rounding :
    HighamCh4KahanReturnedCounterexampleRounding
      highamCh4KahanReturnedCounterexampleP5Format 32 := by
  refine
    { y1 := ?_, s1 := ?_, q1 := ?_, e1 := ?_,
      y2 := ?_, s2 := ?_, q2 := ?_, e2 := ?_,
      y3 := ?_, s3 := ?_, q3 := ?_, e3 := ?_,
      y4 := ?_, s4 := ?_, q4 := ?_, e4 := ?_ }
  all_goals
    norm_num [highamCh4KahanReturnedCounterexampleX1,
      highamCh4KahanReturnedCounterexampleX2,
      highamCh4KahanReturnedCounterexampleX3,
      highamCh4KahanReturnedCounterexampleX4,
      highamCh4KahanReturnedCounterexampleS2,
      highamCh4KahanReturnedCounterexampleY3,
      highamCh4KahanReturnedCounterexampleS3]
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add (-22 : Real) 0 = -22
    exact highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
      (by norm_num [BasicOp.exact])
      highamCh4KahanReturnedCounterexampleP5_finiteSystem_neg22
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add 0 (-22 : Real) = -22
    exact highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
      (by norm_num [BasicOp.exact])
      highamCh4KahanReturnedCounterexampleP5_finiteSystem_neg22
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.sub 0 (-22 : Real) = 22
    exact highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
      (by norm_num [BasicOp.exact]; rfl)
      highamCh4KahanReturnedCounterexampleP5_finiteSystem_pos22
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add 22 (-22 : Real) = 0
    exact highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
      (by norm_num [BasicOp.exact]; rfl)
      highamCh4KahanReturnedCounterexampleP5_finiteSystem_zero
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add (-68 : Real) 0 = -68
    exact highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
      (by norm_num [BasicOp.exact])
      highamCh4KahanReturnedCounterexampleP5_finiteSystem_neg68
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add (-22 : Real) (-68) = -88
    change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
        (BasicOp.exact BasicOp.add (-22 : Real) (-68)) = -88
    norm_num [BasicOp.exact]
    exact
      highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_neg90
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.sub (-22 : Real) (-88) = 64
    change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
        (BasicOp.exact BasicOp.sub (-22 : Real) (-88)) = 64
    norm_num [BasicOp.exact]
    exact
      highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_66
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add 64 (-68 : Real) = -4
    exact highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
      (by norm_num [BasicOp.exact])
      highamCh4KahanReturnedCounterexampleP5_finiteSystem_neg4
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add (-248 : Real) (-4) = -256
    change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
        (BasicOp.exact BasicOp.add (-248 : Real) (-4)) = -256
    norm_num [BasicOp.exact]
    exact
      highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_neg252
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add (-88 : Real) (-256) = -352
    change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
        (BasicOp.exact BasicOp.add (-88 : Real) (-256)) = -352
    norm_num [BasicOp.exact]
    exact
      highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_neg344
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.sub (-88 : Real) (-352) = 256
    change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
        (BasicOp.exact BasicOp.sub (-88 : Real) (-352)) = 256
    norm_num [BasicOp.exact]
    exact
      highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_264
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add 256 (-256 : Real) = 0
    exact highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
      (by norm_num [BasicOp.exact]; rfl)
      highamCh4KahanReturnedCounterexampleP5_finiteSystem_zero
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add 8 0 = (8 : Real)
    exact highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
      (by norm_num [BasicOp.exact])
      highamCh4KahanReturnedCounterexampleP5_finiteSystem_pos8
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add (-352 : Real) 8 = -352
    change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
        (BasicOp.exact BasicOp.add (-352 : Real) 8) = -352
    norm_num [BasicOp.exact]
    exact
      highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_neg344
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.sub (-352 : Real) (-352) = 0
    exact highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
      (by norm_num [BasicOp.exact]; rfl)
      highamCh4KahanReturnedCounterexampleP5_finiteSystem_zero
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add 0 8 = (8 : Real)
    exact highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
      (by norm_num [BasicOp.exact])
      highamCh4KahanReturnedCounterexampleP5_finiteSystem_pos8

/-- The four-term returned-Kahan counterexample trace finishes with stored sum
`-(10p+32)` and retained correction `8`. -/
theorem highamCh4KahanReturnedCounterexampleState_eq_of_rounding
    (fmt : FloatingPointFormat) {p : Real}
    (hround : HighamCh4KahanReturnedCounterexampleRounding fmt p) :
    finiteKahanState fmt 4
        (highamCh4KahanReturnedCounterexampleInput p) =
      { s := highamCh4KahanReturnedCounterexampleS3 p,
        e := highamCh4KahanReturnedCounterexampleX4 } := by
  norm_num [finiteKahanState, finiteKahanPrefixState, finiteKahanStep,
    finiteKahanStepTrace, KahanStepTrace.nextState, KahanState.zero,
    highamCh4KahanReturnedCounterexampleInput, Fin.foldl_succ,
    hround.y1, hround.s1, hround.q1, hround.e1, hround.y2,
    hround.s2, hround.q2, hround.e2, hround.y3, hround.s3,
    hround.q3, hround.e3, hround.y4, hround.s4, hround.q4,
    hround.e4]

/-- Returned stored sum for the four-term counterexample trace. -/
theorem highamCh4KahanReturnedCounterexampleSum_eq_of_rounding
    (fmt : FloatingPointFormat) {p : Real}
    (hround : HighamCh4KahanReturnedCounterexampleRounding fmt p) :
    finiteKahanSum fmt 4
        (highamCh4KahanReturnedCounterexampleInput p) =
      highamCh4KahanReturnedCounterexampleS3 p := by
  have hstate :=
    highamCh4KahanReturnedCounterexampleState_eq_of_rounding fmt hround
  simpa [finiteKahanSum] using congrArg KahanState.s hstate

/-- Retained correction for the four-term counterexample trace. -/
theorem highamCh4KahanReturnedCounterexampleCorrection_eq_of_rounding
    (fmt : FloatingPointFormat) {p : Real}
    (hround : HighamCh4KahanReturnedCounterexampleRounding fmt p) :
    finiteKahanCorrection fmt 4
        (highamCh4KahanReturnedCounterexampleInput p) =
      highamCh4KahanReturnedCounterexampleX4 := by
  have hstate :=
    highamCh4KahanReturnedCounterexampleState_eq_of_rounding fmt hround
  simpa [finiteKahanCorrection] using congrArg KahanState.e hstate

/-- Exact sum of the four-term returned-Kahan counterexample input. -/
theorem highamCh4KahanReturnedCounterexample_exactSum (p : Real) :
    Finset.univ.sum (fun i : Fin 4 =>
      highamCh4KahanReturnedCounterexampleInput p i) =
      -(10 * p + 10) := by
  rw [Fin.sum_univ_four]
  norm_num [highamCh4KahanReturnedCounterexampleInput,
    highamCh4KahanReturnedCounterexampleX1,
    highamCh4KahanReturnedCounterexampleX2,
    highamCh4KahanReturnedCounterexampleX3,
    highamCh4KahanReturnedCounterexampleX4]
  ring_nf

/-- Absolute input sum for the returned-Kahan counterexample when `p >= 1`. -/
theorem highamCh4KahanReturnedCounterexample_absSum
    (p : Real) (hp : 1 <= p) :
    Finset.univ.sum (fun i : Fin 4 =>
      |highamCh4KahanReturnedCounterexampleInput p i|) =
      10 * p + 26 := by
  rw [Fin.sum_univ_four]
  norm_num [highamCh4KahanReturnedCounterexampleInput,
    highamCh4KahanReturnedCounterexampleX1,
    highamCh4KahanReturnedCounterexampleX2,
    highamCh4KahanReturnedCounterexampleX3,
    highamCh4KahanReturnedCounterexampleX4]
  rw [abs_of_nonpos (by nlinarith : -4 + -(2 * p) <= 0)]
  rw [abs_of_nonpos (by nlinarith : 8 - 8 * p <= 0)]
  nlinarith

/-- Any source-weight representation of the returned value for the four-term
finite trace needs total coefficient budget at least the observed returned
error `22`. -/
theorem highamCh4KahanReturnedCounterexample_productLowerBound
    (fmt : FloatingPointFormat) {p b : Real}
    (hp : 1 <= p)
    (hround : HighamCh4KahanReturnedCounterexampleRounding fmt p)
    (mu : Fin 4 -> Real)
    (hmu : highamCh4KahanReturnedCounterexampleMuBound b mu)
    (hrep :
      finiteKahanSum fmt 4
          (highamCh4KahanReturnedCounterexampleInput p) =
        Finset.univ.sum (fun i : Fin 4 =>
          highamCh4KahanReturnedCounterexampleInput p i * (1 + mu i))) :
    22 <= (10 * p + 26) * b := by
  have hreturned :=
    highamCh4KahanReturnedCounterexampleSum_eq_of_rounding fmt hround
  have hreturned' :
      finiteKahanSum fmt 4
          (highamCh4KahanReturnedCounterexampleInput p) =
        -(10 * p + 32) := by
    simpa [highamCh4KahanReturnedCounterexampleS3] using hreturned
  have hexact := highamCh4KahanReturnedCounterexample_exactSum p
  have hsplit :
      Finset.univ.sum (fun i : Fin 4 =>
          highamCh4KahanReturnedCounterexampleInput p i * (1 + mu i)) =
        Finset.univ.sum (fun i : Fin 4 =>
          highamCh4KahanReturnedCounterexampleInput p i) +
        Finset.univ.sum (fun i : Fin 4 =>
          highamCh4KahanReturnedCounterexampleInput p i * mu i) := by
    calc
      Finset.univ.sum (fun i : Fin 4 =>
          highamCh4KahanReturnedCounterexampleInput p i * (1 + mu i)) =
          Finset.univ.sum (fun i : Fin 4 =>
            highamCh4KahanReturnedCounterexampleInput p i +
              highamCh4KahanReturnedCounterexampleInput p i * mu i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = Finset.univ.sum (fun i : Fin 4 =>
            highamCh4KahanReturnedCounterexampleInput p i) +
          Finset.univ.sum (fun i : Fin 4 =>
            highamCh4KahanReturnedCounterexampleInput p i * mu i) := by
            rw [Finset.sum_add_distrib]
  have hmu_sum :
      Finset.univ.sum (fun i : Fin 4 =>
        highamCh4KahanReturnedCounterexampleInput p i * mu i) = -22 := by
    nlinarith [hrep, hreturned', hexact, hsplit]
  have habs_sum :
      |Finset.univ.sum (fun i : Fin 4 =>
          highamCh4KahanReturnedCounterexampleInput p i * mu i)| <=
        Finset.univ.sum (fun i : Fin 4 =>
          |highamCh4KahanReturnedCounterexampleInput p i * mu i|) := by
    simpa using
      (Finset.abs_sum_le_sum_abs
        (fun i : Fin 4 =>
          highamCh4KahanReturnedCounterexampleInput p i * mu i)
        Finset.univ)
  have hterm : forall i : Fin 4,
      |highamCh4KahanReturnedCounterexampleInput p i * mu i| <=
        |highamCh4KahanReturnedCounterexampleInput p i| * b := by
    intro i
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hmu i)
      (abs_nonneg (highamCh4KahanReturnedCounterexampleInput p i))
  have hsum_le :
      Finset.univ.sum (fun i : Fin 4 =>
          |highamCh4KahanReturnedCounterexampleInput p i * mu i|) <=
        Finset.univ.sum (fun i : Fin 4 =>
          |highamCh4KahanReturnedCounterexampleInput p i| * b) := by
    exact Finset.sum_le_sum (by intro i _hi; exact hterm i)
  have hsum_mul :
      Finset.univ.sum (fun i : Fin 4 =>
          |highamCh4KahanReturnedCounterexampleInput p i| * b) =
        (Finset.univ.sum (fun i : Fin 4 =>
          |highamCh4KahanReturnedCounterexampleInput p i|)) * b := by
    rw [Finset.sum_mul]
  have habs_eq :
      |Finset.univ.sum (fun i : Fin 4 =>
        highamCh4KahanReturnedCounterexampleInput p i * mu i)| = 22 := by
    rw [hmu_sum]
    norm_num
  have hchain :
      22 <=
        (Finset.univ.sum (fun i : Fin 4 =>
          |highamCh4KahanReturnedCounterexampleInput p i|)) * b := by
    rw [<- habs_eq]
    exact habs_sum.trans (hsum_le.trans (le_of_eq hsum_mul))
  rw [highamCh4KahanReturnedCounterexample_absSum p hp] at hchain
  exact hchain

/-- Quantitative lower bound on the maximum source coefficient for any
source-weight representation of the returned counterexample value. -/
theorem highamCh4KahanReturnedCounterexample_muLowerBound
    (fmt : FloatingPointFormat) {p b : Real}
    (hp : 1 <= p)
    (hround : HighamCh4KahanReturnedCounterexampleRounding fmt p)
    (mu : Fin 4 -> Real)
    (hmu : highamCh4KahanReturnedCounterexampleMuBound b mu)
    (hrep :
      finiteKahanSum fmt 4
          (highamCh4KahanReturnedCounterexampleInput p) =
        Finset.univ.sum (fun i : Fin 4 =>
          highamCh4KahanReturnedCounterexampleInput p i * (1 + mu i))) :
    22 / (10 * p + 26) <= b := by
  have hprod :=
    highamCh4KahanReturnedCounterexample_productLowerBound
      fmt hp hround mu hmu hrep
  have hden : 0 < 10 * p + 26 := by nlinarith
  exact (div_le_iff₀ hden).mpr (by nlinarith [hprod])

/-- If a proposed uniform source-weight budget is below the forced lower bound
`22/(10p+26)`, then the returned trace cannot have such a representation. -/
theorem highamCh4KahanReturnedCounterexample_no_source_bound_of_lt
    (fmt : FloatingPointFormat) {p b : Real}
    (hp : 1 <= p)
    (hround : HighamCh4KahanReturnedCounterexampleRounding fmt p)
    (hb : b < 22 / (10 * p + 26)) :
    Not (Exists fun
      (mu : HighamCh4KahanReturnedCounterexampleWeight) =>
        highamCh4KahanReturnedCounterexampleSourceRepresentation
          fmt p b mu) := by
  intro h
  cases h with
  | intro mu hrep =>
      cases hrep with
      | intro hmu hsum =>
          have hbound :=
            highamCh4KahanReturnedCounterexample_muLowerBound
              fmt hp hround mu hmu hsum
          nlinarith

/-- Conditional asymptotic obstruction: for any returned trace satisfying the
same identities at scale `p > 26`, the pure first-order budget `2/p` is too
small for a source-weight representation. -/
theorem highamCh4KahanReturnedCounterexample_no_source_bound_two_div_p
    (fmt : FloatingPointFormat) {p : Real}
    (hp : 26 < p)
    (hround : HighamCh4KahanReturnedCounterexampleRounding fmt p) :
    Not (Exists fun
      (mu : HighamCh4KahanReturnedCounterexampleWeight) =>
        highamCh4KahanReturnedCounterexampleSourceRepresentation
          fmt p (2 / p) mu) := by
  have hp_one : 1 <= p := by nlinarith
  apply highamCh4KahanReturnedCounterexample_no_source_bound_of_lt
    fmt hp_one hround
  have hp_pos : 0 < p := by nlinarith
  have hden : 0 < 10 * p + 26 := by nlinarith
  rw [div_lt_div_iff₀ hp_pos hden]
  nlinarith

/-- Local inequalities used in the suffix-recurrence audit for the remaining
returned-Kahan coefficient blocker.  This predicate deliberately mirrors the
available local facts, rather than claiming that the coefficients come from an
actual floating-point trace. -/
def highamCh4KahanSuffixCounterexampleLocalFacts
    (u : Real) (step : KahanCoupledCoeffStep)
    (deltaSub deltaY : Real) : Prop :=
  |step.totalStateCoeff - 1| <= 3 * u ^ 2 ∧
  |step.totalInputCoeff - 1| <= 2 * u + 9 * u ^ 2 ∧
  |step.C| <= u * (1 + u) ^ 2 ∧
  |step.correctionResidualCoeff| <= u * (1 + u) ^ 2 * (3 + u) ∧
  |step.correctionResidualCoeff + deltaSub| <= 7 * u ^ 2 ∧
  |step.residualCoeff - step.correctionResidualCoeff - deltaY| <= u ^ 2 ∧
  |step.residualCoeff + deltaSub - deltaY| <= 8 * u ^ 2 ∧
  |deltaSub| <= u ∧
  |deltaY| <= u

/-- First step of the two-step symbolic suffix-recurrence counterexample
suggested by the GPT-5.5 Pro proof-route audit. -/
def highamCh4KahanSuffixCounterexampleStep1
    (u : Real) : KahanCoupledCoeffStep :=
  { A := 1
    B := 1 + u
    C := 0
    D := u + u ^ 2
    x := 0 }

/-- Second step of the two-step symbolic suffix-recurrence counterexample. -/
def highamCh4KahanSuffixCounterexampleStep2
    (u : Real) : KahanCoupledCoeffStep :=
  { A := 1 + u
    B := 1 + u
    C := -u
    D := -u
    x := 0 }

/-- Returned coefficient after injecting a source at step 1 and propagating it
through the second symbolic suffix step. -/
def highamCh4KahanSuffixCounterexampleReturnedCoeff
    (u : Real) : Real :=
  KahanState.returnedFromTotalCorrection
    ((highamCh4KahanSuffixCounterexampleStep2 u).propagateTotalCorrection
      { s := (highamCh4KahanSuffixCounterexampleStep1 u).totalInputCoeff
        e := (highamCh4KahanSuffixCounterexampleStep1 u).D })

theorem highamCh4KahanSuffixCounterexampleReturnedCoeff_eq (u : Real) :
    highamCh4KahanSuffixCounterexampleReturnedCoeff u = (1 + u) ^ 3 := by
  dsimp [highamCh4KahanSuffixCounterexampleReturnedCoeff,
    highamCh4KahanSuffixCounterexampleStep1,
    highamCh4KahanSuffixCounterexampleStep2,
    KahanState.returnedFromTotalCorrection,
    KahanCoupledCoeffStep.propagateTotalCorrection,
    KahanCoupledCoeffStep.totalStateCoeff,
    KahanCoupledCoeffStep.totalInputCoeff,
    KahanCoupledCoeffStep.residualCoeff,
    KahanCoupledCoeffStep.correctionResidualCoeff]
  ring

/-- One-step majorant update for the corrected leading-`3*u` suffix audit.
This is the Lean-facing arithmetic core of the GPT-5.5 Pro follow-up: if the
paired-total error `alpha` is already at most first-order small and the retained
correction majorant `beta` is at most `3*u`, then the local recurrence increases
`alpha` by only `13*u^2` and preserves `beta <= 3*u`. -/
theorem highamCh4KahanSuffixMajorant_step
    {u alpha beta alphaNext betaNext : Real}
    (hu0 : 0 <= u) (hu64 : u <= 1 / 64)
    (halpha : alpha <= 1) (hbeta : beta <= 3 * u)
    (halphaNext :
      alphaNext <= alpha + 3 * u ^ 2 * (1 + alpha) +
        (2 * u + 8 * u ^ 2) * beta)
    (hbetaNext :
      betaNext <= u * (1 + u) ^ 2 * (1 + alpha) +
        (u + 7 * u ^ 2) * beta) :
    alphaNext <= alpha + 13 * u ^ 2 ∧ betaNext <= 3 * u := by
  constructor
  · nlinarith [hu0, hu64, halpha, hbeta, halphaNext]
  · have hfac_nonneg : 0 <= u * (1 + u) ^ 2 := by
      exact mul_nonneg hu0 (sq_nonneg (1 + u))
    have hterm1_le :
        u * (1 + u) ^ 2 * (1 + alpha) <=
          u * (1 + u) ^ 2 * 2 := by
      exact mul_le_mul_of_nonneg_left (by nlinarith [halpha]) hfac_nonneg
    have hterm1 :
        u * (1 + u) ^ 2 * (1 + alpha) <= (9 / 4) * u := by
      nlinarith [hterm1_le, hu0, hu64, sq_nonneg u,
        mul_nonneg (sq_nonneg u) hu0]
    have hcoef_nonneg : 0 <= u + 7 * u ^ 2 := by
      nlinarith [hu0, sq_nonneg u]
    have hterm2_le :
        (u + 7 * u ^ 2) * beta <= (u + 7 * u ^ 2) * (3 * u) := by
      exact mul_le_mul_of_nonneg_left hbeta hcoef_nonneg
    have hterm2 :
        (u + 7 * u ^ 2) * beta <= (3 / 4) * u := by
      nlinarith [hterm2_le, hu0, hu64, sq_nonneg u,
        mul_nonneg (sq_nonneg u) hu0]
    nlinarith

/-- Sequence-level corrected leading-`3*u` suffix majorant.  This theorem is
still an audit theorem: it proves the majorant recurrence once the `alpha` and
`beta` update inequalities have been supplied, but it does not itself derive
those updates from an arbitrary finite Kahan trace. -/
theorem highamCh4KahanSuffixMajorant_recurrence
    {u : Real} {m : Nat} {alpha beta : Nat -> Real}
    (hu0 : 0 <= u) (hu64 : u <= 1 / 64)
    (hm : (m : Real) * u ^ 2 <= 1 / 16)
    (halpha0 : alpha 0 <= 2 * u + 9 * u ^ 2)
    (hbeta0 : beta 0 <= 3 * u)
    (halphaNext : ∀ j, j < m ->
      alpha (j + 1) <= alpha j + 3 * u ^ 2 * (1 + alpha j) +
        (2 * u + 8 * u ^ 2) * beta j)
    (hbetaNext : ∀ j, j < m ->
      beta (j + 1) <= u * (1 + u) ^ 2 * (1 + alpha j) +
        (u + 7 * u ^ 2) * beta j) :
    ∀ j, j <= m ->
      alpha j <= 2 * u + (9 + 13 * (j : Real)) * u ^ 2 ∧
        beta j <= 3 * u := by
  intro j hj
  induction j with
  | zero =>
      constructor
      · simpa using halpha0
      · simpa using hbeta0
  | succ j ih =>
      have hjm : j < m := Nat.lt_of_succ_le hj
      have hjle : j <= m := Nat.le_of_lt hjm
      have hih := ih hjle
      have hju2 : (j : Real) * u ^ 2 <= (m : Real) * u ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjle) (sq_nonneg u)
      have halpha_le_one : alpha j <= 1 := by
        have hju2_nonneg : 0 <= (j : Real) * u ^ 2 := by
          exact mul_nonneg (by exact_mod_cast Nat.zero_le j) (sq_nonneg u)
        nlinarith [hih.1, hju2, hju2_nonneg, hm, hu0, hu64, sq_nonneg u]
      have hstep :=
        highamCh4KahanSuffixMajorant_step
          hu0 hu64 halpha_le_one hih.2
          (halphaNext j hjm) (hbetaNext j hjm)
      constructor
      · norm_num [Nat.cast_succ]
        nlinarith [hih.1, hstep.1]
      · exact hstep.2

/-- The local suffix facts imply the corrected leading-`3*u` majorant update
for one abstract `(z,q)` propagation step. -/
theorem highamCh4KahanSuffixMajorant_update_of_localFacts
    {u z q deltaSub deltaY : Real} {step : KahanCoupledCoeffStep}
    (hu0 : 0 <= u)
    (hlocal :
      highamCh4KahanSuffixCounterexampleLocalFacts u step deltaSub deltaY) :
    |(step.totalStateCoeff * z + step.residualCoeff * q) - 1| <=
        |z - 1| + 3 * u ^ 2 * (1 + |z - 1|) +
          (2 * u + 8 * u ^ 2) * |q| ∧
      |step.C * z + step.correctionResidualCoeff * q| <=
        u * (1 + u) ^ 2 * (1 + |z - 1|) +
          (u + 7 * u ^ 2) * |q| := by
  rcases hlocal with
    ⟨hts, _htx, hC, _hc, hc_delta, _hr_c_delta, hr_combined, hdeltaSub, hdeltaY⟩
  have hz_abs : |z| <= 1 + |z - 1| := by
    calc
      |z| = |(z - 1) + 1| := by
        congr 1
        ring
      _ <= |z - 1| + |(1 : Real)| := abs_add_le _ _
      _ = 1 + |z - 1| := by ring
  have hr_abs : |step.residualCoeff| <= 2 * u + 8 * u ^ 2 := by
    have hr_decomp :
        step.residualCoeff =
          (step.residualCoeff + deltaSub - deltaY) - deltaSub + deltaY := by
      ring
    calc
      |step.residualCoeff| =
          |(step.residualCoeff + deltaSub - deltaY) - deltaSub + deltaY| := by
        exact congrArg abs hr_decomp
      _ <= |step.residualCoeff + deltaSub - deltaY| +
            |deltaSub| + |deltaY| := by
        calc
          |(step.residualCoeff + deltaSub - deltaY) - deltaSub + deltaY|
              <= |(step.residualCoeff + deltaSub - deltaY) - deltaSub| +
                  |deltaY| := abs_add_le _ _
          _ <= |step.residualCoeff + deltaSub - deltaY| +
                |deltaSub| + |deltaY| := by
            have hsub :
                |(step.residualCoeff + deltaSub - deltaY) - deltaSub| <=
                  |step.residualCoeff + deltaSub - deltaY| + |deltaSub| := by
              simpa [sub_eq_add_neg] using
                abs_add_le (step.residualCoeff + deltaSub - deltaY) (-deltaSub)
            nlinarith
      _ <= 2 * u + 8 * u ^ 2 := by nlinarith
  have hc_tight : |step.correctionResidualCoeff| <= u + 7 * u ^ 2 := by
    have hc_decomp :
        step.correctionResidualCoeff =
          (step.correctionResidualCoeff + deltaSub) - deltaSub := by
      ring
    calc
      |step.correctionResidualCoeff| =
          |(step.correctionResidualCoeff + deltaSub) - deltaSub| := by
        exact congrArg abs hc_decomp
      _ <= |step.correctionResidualCoeff + deltaSub| + |deltaSub| := by
        simpa [sub_eq_add_neg] using
          abs_add_le (step.correctionResidualCoeff + deltaSub) (-deltaSub)
      _ <= u + 7 * u ^ 2 := by nlinarith
  constructor
  · have hdecomp :
        (step.totalStateCoeff * z + step.residualCoeff * q) - 1 =
          (z - 1) + (step.totalStateCoeff - 1) * z +
            step.residualCoeff * q := by
      ring
    have htri :
        |(step.totalStateCoeff * z + step.residualCoeff * q) - 1| <=
          |z - 1| + |(step.totalStateCoeff - 1) * z| +
            |step.residualCoeff * q| := by
      rw [hdecomp]
      calc
        |(z - 1) + (step.totalStateCoeff - 1) * z +
            step.residualCoeff * q|
            <= |(z - 1) + (step.totalStateCoeff - 1) * z| +
                |step.residualCoeff * q| := abs_add_le _ _
        _ <= |z - 1| + |(step.totalStateCoeff - 1) * z| +
              |step.residualCoeff * q| := by
          have hfirst :
              |(z - 1) + (step.totalStateCoeff - 1) * z| <=
                |z - 1| + |(step.totalStateCoeff - 1) * z| := abs_add_le _ _
          nlinarith
    have hts_term :
        |(step.totalStateCoeff - 1) * z| <=
          3 * u ^ 2 * (1 + |z - 1|) := by
      rw [abs_mul]
      exact mul_le_mul hts hz_abs (abs_nonneg z)
        (by nlinarith [sq_nonneg u])
    have hr_term :
        |step.residualCoeff * q| <= (2 * u + 8 * u ^ 2) * |q| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hr_abs (abs_nonneg q)
    nlinarith
  · have htri :
        |step.C * z + step.correctionResidualCoeff * q| <=
          |step.C * z| + |step.correctionResidualCoeff * q| := abs_add_le _ _
    have hC_term :
        |step.C * z| <= u * (1 + u) ^ 2 * (1 + |z - 1|) := by
      rw [abs_mul]
      exact mul_le_mul hC hz_abs (abs_nonneg z)
        (mul_nonneg hu0 (sq_nonneg (1 + u)))
    have hc_term :
        |step.correctionResidualCoeff * q| <= (u + 7 * u ^ 2) * |q| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hc_tight (abs_nonneg q)
    nlinarith

/-- Auxiliary list propagation theorem for the corrected leading-`3*u`
suffix majorant.  Starting from an arbitrary paired-total radius `base`, each
local-fact step increases the paired-total radius by at most `13*u^2` and keeps
the retained correction within `3*u`. -/
theorem highamCh4KahanSuffixMajorant_propagate_of_localFacts_aux
    {u base : Real} {steps : List KahanCoupledCoeffStep} {init : KahanState}
    (hu0 : 0 <= u) (hu64 : u <= 1 / 64)
    (hbudget : base + 13 * (steps.length : Real) * u ^ 2 <= 1)
    (hlocal : ∀ i : Fin steps.length, ∃ deltaSub deltaY : Real,
      highamCh4KahanSuffixCounterexampleLocalFacts u (steps.get i)
        deltaSub deltaY)
    (hinitS : |init.s - 1| <= base)
    (hinitE : |init.e| <= 3 * u) :
    let final := kahanCoupledTotalCorrectionPropagate steps init
    |final.s - 1| <= base + 13 * (steps.length : Real) * u ^ 2 ∧
      |final.e| <= 3 * u := by
  induction steps generalizing init base with
  | nil =>
      dsimp [kahanCoupledTotalCorrectionPropagate]
      constructor
      · simpa using hinitS
      · simpa using hinitE
  | cons step tail ih =>
      have hhead :
          ∃ deltaSub deltaY : Real,
            highamCh4KahanSuffixCounterexampleLocalFacts u step
              deltaSub deltaY := by
        simpa using hlocal ⟨0, by simp⟩
      rcases hhead with ⟨deltaSub, deltaY, hstepLocal⟩
      let next := step.propagateTotalCorrection init
      have hupdate :=
        highamCh4KahanSuffixMajorant_update_of_localFacts
          (u := u) (z := init.s) (q := init.e)
          (deltaSub := deltaSub) (deltaY := deltaY)
          (step := step) hu0 hstepLocal
      have hnextS_update :
          |next.s - 1| <= |init.s - 1| +
            3 * u ^ 2 * (1 + |init.s - 1|) +
              (2 * u + 8 * u ^ 2) * |init.e| := by
        simpa [next, KahanCoupledCoeffStep.propagateTotalCorrection,
          mul_comm, mul_left_comm, mul_assoc] using hupdate.1
      have hnextE_update :
          |next.e| <= u * (1 + u) ^ 2 * (1 + |init.s - 1|) +
            (u + 7 * u ^ 2) * |init.e| := by
        simpa [next, KahanCoupledCoeffStep.propagateTotalCorrection,
          mul_comm, mul_left_comm, mul_assoc] using hupdate.2
      have hlen_nonneg : 0 <= 13 * ((step :: tail).length : Real) * u ^ 2 := by
        exact mul_nonneg
          (mul_nonneg (by norm_num)
            (by exact_mod_cast Nat.zero_le (step :: tail).length))
          (sq_nonneg u)
      have hbase_le_one : base <= 1 := by nlinarith
      have halpha_le_one : |init.s - 1| <= 1 := by nlinarith [hinitS, hbase_le_one]
      have hmajorantStep :=
        highamCh4KahanSuffixMajorant_step
          hu0 hu64 halpha_le_one hinitE hnextS_update hnextE_update
      have hnextS :
          |next.s - 1| <= base + 13 * u ^ 2 := by
        nlinarith [hinitS, hmajorantStep.1]
      have htailBudget :
          (base + 13 * u ^ 2) + 13 * (tail.length : Real) * u ^ 2 <= 1 := by
        norm_num [Nat.cast_succ] at hbudget ⊢
        nlinarith
      have htailLocal :
          ∀ i : Fin tail.length, ∃ deltaSub deltaY : Real,
            highamCh4KahanSuffixCounterexampleLocalFacts u (tail.get i)
              deltaSub deltaY := by
        intro i
        have h := hlocal ⟨i.val + 1, by simp [i.isLt]⟩
        simpa using h
      have htail :=
        ih htailBudget htailLocal hnextS hmajorantStep.2
      dsimp [kahanCoupledTotalCorrectionPropagate]
      simpa [next, Nat.cast_succ, add_assoc, add_left_comm, add_comm,
        mul_add, add_mul] using htail

/-- Corrected leading-`3*u` list propagation theorem for the local suffix
facts.  This does not close Higham's printed leading-`2*u` Eq. (4.8); it is a
checked corrected route for the currently available local facts. -/
theorem highamCh4KahanSuffixMajorant_propagate_of_localFacts
    {u : Real} {steps : List KahanCoupledCoeffStep} {init : KahanState}
    (hu0 : 0 <= u) (hu64 : u <= 1 / 64)
    (hm : (steps.length : Real) * u ^ 2 <= 1 / 16)
    (hlocal : ∀ i : Fin steps.length, ∃ deltaSub deltaY : Real,
      highamCh4KahanSuffixCounterexampleLocalFacts u (steps.get i)
        deltaSub deltaY)
    (hinitS : |init.s - 1| <= 2 * u + 9 * u ^ 2)
    (hinitE : |init.e| <= 3 * u) :
    let final := kahanCoupledTotalCorrectionPropagate steps init
    |final.s - 1| <= 2 * u + (9 + 13 * (steps.length : Real)) * u ^ 2 ∧
      |final.e| <= 3 * u := by
  have hbudget :
      (2 * u + 9 * u ^ 2) + 13 * (steps.length : Real) * u ^ 2 <= 1 := by
    nlinarith [hu0, hu64, hm, sq_nonneg u]
  have h :=
    highamCh4KahanSuffixMajorant_propagate_of_localFacts_aux
      (u := u) (base := 2 * u + 9 * u ^ 2)
      (steps := steps) (init := init)
      hu0 hu64 hbudget hlocal hinitS hinitE
  simpa [add_assoc, add_left_comm, add_comm, right_distrib, mul_add,
    mul_comm, mul_left_comm, mul_assoc] using h

/-- The actual indexed Kahan coefficient step satisfies the local-facts
interface used by the suffix recurrence audit. -/
theorem kahanCoupledCoeffStepOfIndex_localFacts
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (i : Fin n)
    (hu1 : fp.u <= 1) :
    highamCh4KahanSuffixCounterexampleLocalFacts fp.u
      (kahanCoupledCoeffStepOfIndex fp v i)
      (kahanTrace_deltaWitness fp v i).deltaSub
      (kahanTrace_deltaWitness fp v i).deltaY := by
  dsimp [highamCh4KahanSuffixCounterexampleLocalFacts]
  constructor
  · exact
      kahanCoupledCoeffStepOfIndex_totalStateCoeff_abs_sub_one_le_three_u_sq
        fp v i hu1
  constructor
  · exact
      kahanCoupledCoeffStepOfIndex_totalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
        fp v i hu1
  constructor
  · exact kahanCoupledCoeffStepOfIndex_C_abs_le fp v i
  constructor
  · exact kahanCoupledCoeffStepOfIndex_correctionResidualCoeff_abs_le fp v i
  constructor
  · exact
      kahanCoupledCoeffStepOfIndex_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq
        fp v i hu1
  constructor
  · exact
      kahanCoupledCoeffStepOfIndex_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq
        fp v i
  constructor
  · exact
      kahanCoupledCoeffStepOfIndex_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq
        fp v i hu1
  constructor
  · exact (kahanTrace_deltaWitness fp v i).h_deltaSub
  · exact (kahanTrace_deltaWitness fp v i).h_deltaY

/-- The actual coefficient-step list supplies local-facts witnesses for every
suffix index. -/
theorem kahanCoupledCoeffSteps_localFacts
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (k : Nat) (hk : k <= n)
    (hu1 : fp.u <= 1) :
    forall i : Fin (kahanCoupledCoeffSteps fp v k hk).length,
      exists deltaSub deltaY : Real,
        highamCh4KahanSuffixCounterexampleLocalFacts fp.u
          ((kahanCoupledCoeffSteps fp v k hk).get i)
          deltaSub deltaY := by
  intro i
  have hik : i.val < k := by
    simpa [kahanCoupledCoeffSteps] using i.isLt
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le hik hk⟩
  refine
    ⟨(kahanTrace_deltaWitness fp v idx).deltaSub,
      (kahanTrace_deltaWitness fp v idx).deltaY, ?_⟩
  simpa [kahanCoupledCoeffSteps, idx] using
    kahanCoupledCoeffStepOfIndex_localFacts fp v idx hu1

/-- Actual-step version of the corrected leading-`3*u` suffix majorant.  This
packages the individual Kahan coefficient-step inequalities into the abstract
local-facts recurrence. -/
theorem kahanCoupledCoeffSteps_totalCorrectionPropagate_abs_le_correctedSuffixMajorant
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (k : Nat) (hk : k <= n)
    (hu64 : fp.u <= 1 / 64)
    (hm : ((kahanCoupledCoeffSteps fp v k hk).length : Real) *
        fp.u ^ 2 <= 1 / 16)
    {init : KahanState}
    (hinitS : |init.s - 1| <= 2 * fp.u + 9 * fp.u ^ 2)
    (hinitE : |init.e| <= 3 * fp.u) :
    let final :=
      kahanCoupledTotalCorrectionPropagate
        (kahanCoupledCoeffSteps fp v k hk) init
    |final.s - 1| <=
        2 * fp.u +
          (9 + 13 * ((kahanCoupledCoeffSteps fp v k hk).length : Real)) *
            fp.u ^ 2 ∧
      |final.e| <= 3 * fp.u := by
  have hu1 : fp.u <= 1 := by nlinarith
  exact
    highamCh4KahanSuffixMajorant_propagate_of_localFacts
      (u := fp.u) (steps := kahanCoupledCoeffSteps fp v k hk)
      (init := init) fp.u_nonneg hu64 hm
      (kahanCoupledCoeffSteps_localFacts fp v k hk hu1)
      hinitS hinitE

/-- Any dropped suffix of the actual coefficient-step list still supplies
local-facts witnesses at every suffix index. -/
theorem kahanCoupledCoeffSteps_drop_localFacts
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (k : Nat) (hk : k <= n)
    (hu1 : fp.u <= 1) (r : Nat) :
    forall i : Fin ((kahanCoupledCoeffSteps fp v k hk).drop r).length,
      exists deltaSub deltaY : Real,
        highamCh4KahanSuffixCounterexampleLocalFacts fp.u
          (((kahanCoupledCoeffSteps fp v k hk).drop r).get i)
          deltaSub deltaY := by
  intro i
  let steps := kahanCoupledCoeffSteps fp v k hk
  have hi_len : i.val < steps.length - r := by
    simpa [steps, List.length_drop] using i.isLt
  have hir : r + i.val < steps.length := by
    simpa [Nat.add_comm] using Nat.add_lt_of_lt_sub hi_len
  let j : Fin steps.length := ⟨r + i.val, hir⟩
  rcases kahanCoupledCoeffSteps_localFacts fp v k hk hu1 j with
    ⟨deltaSub, deltaY, hlocal⟩
  refine ⟨deltaSub, deltaY, ?_⟩
  have hget : (steps.drop r).get i = steps.get j := by
    rw [List.get_eq_getElem, List.get_eq_getElem]
    change (steps.drop r)[i.val] = steps[r + i.val]
    exact List.getElem_drop (xs := steps) (i := r) (j := i.val)
      (h := i.isLt)
  change highamCh4KahanSuffixCounterexampleLocalFacts fp.u
    ((steps.drop r).get i) deltaSub deltaY
  rw [hget]
  simpa [steps] using hlocal

/-- Dropped-suffix version of the corrected leading-`3*u` actual-step
majorant.  This is the reusable suffix handoff for source-coefficient
propagation. -/
theorem kahanCoupledCoeffSteps_drop_totalCorrectionPropagate_abs_le_correctedSuffixMajorant
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (k : Nat) (hk : k <= n)
    (r : Nat)
    (hu64 : fp.u <= 1 / 64)
    (hm : (((kahanCoupledCoeffSteps fp v k hk).drop r).length : Real) *
        fp.u ^ 2 <= 1 / 16)
    {init : KahanState}
    (hinitS : |init.s - 1| <= 2 * fp.u + 9 * fp.u ^ 2)
    (hinitE : |init.e| <= 3 * fp.u) :
    let suffix := (kahanCoupledCoeffSteps fp v k hk).drop r
    let final := kahanCoupledTotalCorrectionPropagate suffix init
    |final.s - 1| <=
        2 * fp.u + (9 + 13 * (suffix.length : Real)) * fp.u ^ 2 ∧
      |final.e| <= 3 * fp.u := by
  have hu1 : fp.u <= 1 := by nlinarith
  exact
    highamCh4KahanSuffixMajorant_propagate_of_localFacts
      (u := fp.u) (steps := (kahanCoupledCoeffSteps fp v k hk).drop r)
      (init := init) fp.u_nonneg hu64 hm
      (kahanCoupledCoeffSteps_drop_localFacts fp v k hk hu1 r)
      hinitS hinitE

/-- Corrected leading-`3*u` paired-coordinate bound for every propagated
source coefficient of the actual Kahan coefficient-step list.  This theorem
specializes the dropped-suffix majorant to the source coefficient injected at
index `i`; it is source-shaped for the compensated-total coordinate, not yet
Higham's ordinary returned-`s` leading-`2*u` theorem. -/
theorem kahanCoupledCoeffSteps_sourceTotalCorrectionCoeff_abs_le_correctedSuffixMajorant
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (k : Nat) (hk : k <= n)
    (hu64 : fp.u <= 1 / 64)
    (i : Fin (kahanCoupledCoeffSteps fp v k hk).length)
    (hm : (((kahanCoupledCoeffSteps fp v k hk).drop (i.val + 1)).length : Real) *
        fp.u ^ 2 <= 1 / 16) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    |(kahanCoupledSourceTotalCorrectionCoeff steps i).s - 1| <=
        2 * fp.u +
          (9 + 13 * ((steps.drop (i.val + 1)).length : Real)) *
            fp.u ^ 2 ∧
      |(kahanCoupledSourceTotalCorrectionCoeff steps i).e| <= 3 * fp.u := by
  have hu1 : fp.u <= 1 := by nlinarith
  let steps := kahanCoupledCoeffSteps fp v k hk
  have hmem : steps.get i ∈ steps := List.get_mem steps i
  have hinitS :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).s - 1| <=
        2 * fp.u + 9 * fp.u ^ 2 := by
    have h :=
      kahanCoupledCoeffSteps_totalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
        fp v k hk hu1 (steps.get i) hmem
    simpa [steps, KahanState.totalCorrection,
      KahanCoupledCoeffStep.sourceCoeff,
      KahanCoupledCoeffStep.totalInputCoeff] using h
  have hinitE :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).e| <=
        3 * fp.u := by
    have hD :=
      kahanCoupledCoeffSteps_D_abs_le fp v k hk (steps.get i) hmem
    have hD3 : fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) <= 3 * fp.u := by
      nlinarith [fp.u_nonneg, hu64, sq_nonneg fp.u,
        mul_nonneg fp.u_nonneg (sq_nonneg (1 + fp.u))]
    have hD_bound : |(steps.get i).D| <= 3 * fp.u := by
      nlinarith
    simpa [steps, KahanState.totalCorrection,
      KahanCoupledCoeffStep.sourceCoeff] using hD_bound
  have hprop :=
    kahanCoupledCoeffSteps_drop_totalCorrectionPropagate_abs_le_correctedSuffixMajorant
      fp v k hk (i.val + 1) hu64 hm hinitS hinitE
  simpa [steps, kahanCoupledSourceCoeff_totalCorrection_eq] using hprop

/-- Final-step returned-coordinate extraction for the corrected ordinary
returned-Kahan route.  If the paired source-total state has leading `2*u`, the
last ordinary returned step contributes the missing main-addition first-order
term, giving leading `3*u`. -/
theorem highamCh4KahanReturnedFinalStep_majorant
    {u a : Real} {step : KahanCoupledCoeffStep} {state : KahanState}
    (hu0 : 0 <= u)
    (hS : |state.s - 1| <= 2 * u + a * u ^ 2)
    (hE : |state.e| <= 3 * u)
    (hA : |step.returnedStateCoeff - 1| <= u)
    (hB : |step.returnedCorrectionCoeff| <= u * (1 + u)) :
    |KahanState.returnedFromTotalCorrection
        (step.propagateTotalCorrection state) - 1| <=
      3 * u + (a + 5) * u ^ 2 + (a + 3) * u ^ 3 := by
  have hbase :=
    KahanCoupledCoeffStep.propagateTotalCorrection_returnedDev_abs_le_of_bounds
      step state hA hB
  have hone : 0 <= 1 + u := by nlinarith
  have htheta : 0 <= u * (1 + u) := mul_nonneg hu0 hone
  have hSstep :
      |state.s - 1| * (1 + u) <=
        (2 * u + a * u ^ 2) * (1 + u) := by
    exact mul_le_mul_of_nonneg_right hS hone
  have hEstep :
      |state.e| * (u * (1 + u)) <=
        (3 * u) * (u * (1 + u)) := by
    exact mul_le_mul_of_nonneg_right hE htheta
  calc
    |KahanState.returnedFromTotalCorrection
        (step.propagateTotalCorrection state) - 1|
        <= |state.s - 1| * (1 + u) + u +
          |state.e| * (u * (1 + u)) := hbase
    _ <= (2 * u + a * u ^ 2) * (1 + u) + u +
          (3 * u) * (u * (1 + u)) := by nlinarith
    _ = 3 * u + (a + 5) * u ^ 2 + (a + 3) * u ^ 3 := by ring

/-- Append-final-step form of the corrected ordinary returned route.  A
paired-coordinate prefix recurrence with leading `2*u` becomes an ordinary
returned-coordinate bound with leading `3*u` after one final returned step. -/
theorem highamCh4KahanReturnedAppendFinal_majorant
    {u : Real} {pref : List KahanCoupledCoeffStep}
    {last : KahanCoupledCoeffStep} {init : KahanState}
    (hu0 : 0 <= u) (hu64 : u <= 1 / 64)
    (hm : (pref.length : Real) * u ^ 2 <= 1 / 16)
    (hlocal : forall i : Fin pref.length, exists deltaSub deltaY : Real,
      highamCh4KahanSuffixCounterexampleLocalFacts u (pref.get i)
        deltaSub deltaY)
    (hinitS : |init.s - 1| <= 2 * u + 9 * u ^ 2)
    (hinitE : |init.e| <= 3 * u)
    (hA : |last.returnedStateCoeff - 1| <= u)
    (hB : |last.returnedCorrectionCoeff| <= u * (1 + u)) :
    |KahanState.returnedFromTotalCorrection
        (kahanCoupledTotalCorrectionPropagate (pref ++ [last]) init) - 1| <=
      3 * u +
        ((9 + 13 * (pref.length : Real)) + 5) * u ^ 2 +
          ((9 + 13 * (pref.length : Real)) + 3) * u ^ 3 := by
  let mid := kahanCoupledTotalCorrectionPropagate pref init
  have hprefix :=
    highamCh4KahanSuffixMajorant_propagate_of_localFacts
      (u := u) (steps := pref) (init := init)
      hu0 hu64 hm hlocal hinitS hinitE
  have hfold :
      kahanCoupledTotalCorrectionPropagate (pref ++ [last]) init =
        last.propagateTotalCorrection mid := by
    dsimp [kahanCoupledTotalCorrectionPropagate, mid]
    simp [List.foldl_append]
  rw [hfold]
  exact
    highamCh4KahanReturnedFinalStep_majorant
      (u := u) (a := 9 + 13 * (pref.length : Real))
      (step := last) (state := mid)
      hu0 hprefix.1 hprefix.2 hA hB

/-- Nonempty-list form of the corrected ordinary returned route, splitting the
list at its final step. -/
theorem highamCh4KahanReturnedNonempty_majorant
    {u : Real} {steps : List KahanCoupledCoeffStep} {init : KahanState}
    (hne : Not (steps = []))
    (hu0 : 0 <= u) (hu64 : u <= 1 / 64)
    (hm : (steps.dropLast.length : Real) * u ^ 2 <= 1 / 16)
    (hlocal : forall i : Fin steps.dropLast.length, exists deltaSub deltaY : Real,
      highamCh4KahanSuffixCounterexampleLocalFacts u (steps.dropLast.get i)
        deltaSub deltaY)
    (hinitS : |init.s - 1| <= 2 * u + 9 * u ^ 2)
    (hinitE : |init.e| <= 3 * u)
    (hA : |(steps.getLast hne).returnedStateCoeff - 1| <= u)
    (hB : |(steps.getLast hne).returnedCorrectionCoeff| <= u * (1 + u)) :
    |KahanState.returnedFromTotalCorrection
        (kahanCoupledTotalCorrectionPropagate steps init) - 1| <=
      3 * u +
        ((9 + 13 * (steps.dropLast.length : Real)) + 5) * u ^ 2 +
          ((9 + 13 * (steps.dropLast.length : Real)) + 3) * u ^ 3 := by
  have hdecomp :
      kahanCoupledTotalCorrectionPropagate steps init =
        kahanCoupledTotalCorrectionPropagate
          (steps.dropLast ++ [steps.getLast hne]) init := by
    rw [List.dropLast_append_getLast hne]
  rw [hdecomp]
  exact
    highamCh4KahanReturnedAppendFinal_majorant
      (u := u) (pref := steps.dropLast) (last := steps.getLast hne)
      (init := init) hu0 hu64 hm hlocal hinitS hinitE hA hB

/-- Membership version of the actual-step local-facts package. -/
theorem kahanCoupledCoeffSteps_localFacts_of_mem
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (k : Nat) (hk : k <= n)
    (hu1 : fp.u <= 1) {step : KahanCoupledCoeffStep}
    (hmem : step ∈ kahanCoupledCoeffSteps fp v k hk) :
    exists deltaSub deltaY : Real,
      highamCh4KahanSuffixCounterexampleLocalFacts fp.u step
        deltaSub deltaY := by
  let steps := kahanCoupledCoeffSteps fp v k hk
  have hmem' : step ∈ steps := by simpa [steps] using hmem
  rcases List.get_of_mem hmem' with ⟨idx, hidx⟩
  rcases kahanCoupledCoeffSteps_localFacts fp v k hk hu1 idx with
    ⟨deltaSub, deltaY, hlocal⟩
  refine ⟨deltaSub, deltaY, ?_⟩
  rw [← hidx]
  simpa [steps] using hlocal

/-- Local `B`-coefficient bound for an actual coupled Kahan step.  This handles
the empty-suffix source-coefficient case. -/
theorem kahanCoupledCoeffStepOfIndex_B_abs_sub_one_le_two_u_plus_u_sq
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (i : Fin n) :
    |(kahanCoupledCoeffStepOfIndex fp v i).B - 1| <=
      2 * fp.u + fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfIndex] using
    kahanTrace_deltaWitness_storedSumInputCoeff_abs_sub_one_le_two_u_plus_u_sq
      fp v i

/-- Corrected ordinary returned source-coefficient bound for a nonempty suffix.
This is the main checked Lean translation of the whole-problem GPT-5.5 Pro
audit's leading-`3*u` route. -/
theorem kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_correctedReturnedMajorant_nonempty
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (k : Nat) (hk : k <= n)
    (hu64 : fp.u <= 1 / 64)
    (i : Fin (kahanCoupledCoeffSteps fp v k hk).length)
    (hne :
      Not (((kahanCoupledCoeffSteps fp v k hk).drop (i.val + 1)) = []))
    (hm :
      ((((kahanCoupledCoeffSteps fp v k hk).drop (i.val + 1)).dropLast.length : Real) *
          fp.u ^ 2 <= 1 / 16)) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    let suffix := steps.drop (i.val + 1)
    |(kahanCoupledSourceCoeff steps i).s - 1| <=
      3 * fp.u +
        ((9 + 13 * (suffix.dropLast.length : Real)) + 5) * fp.u ^ 2 +
          ((9 + 13 * (suffix.dropLast.length : Real)) + 3) * fp.u ^ 3 := by
  have hu1 : fp.u <= 1 := by nlinarith
  let steps := kahanCoupledCoeffSteps fp v k hk
  let suffix := steps.drop (i.val + 1)
  have hmem : steps.get i ∈ steps := List.get_mem steps i
  have hinitS :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).s - 1| <=
        2 * fp.u + 9 * fp.u ^ 2 := by
    have h :=
      kahanCoupledCoeffSteps_totalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
        fp v k hk hu1 (steps.get i) hmem
    simpa [steps, KahanState.totalCorrection,
      KahanCoupledCoeffStep.sourceCoeff,
      KahanCoupledCoeffStep.totalInputCoeff] using h
  have hinitE :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).e| <=
        3 * fp.u := by
    have hD :=
      kahanCoupledCoeffSteps_D_abs_le fp v k hk (steps.get i) hmem
    have hD3 : fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) <= 3 * fp.u := by
      nlinarith [fp.u_nonneg, hu64, sq_nonneg fp.u,
        mul_nonneg fp.u_nonneg (sq_nonneg (1 + fp.u))]
    have hD_bound : |(steps.get i).D| <= 3 * fp.u := by
      nlinarith
    simpa [steps, KahanState.totalCorrection,
      KahanCoupledCoeffStep.sourceCoeff] using hD_bound
  have hprefixLocal :
      forall j : Fin suffix.dropLast.length, exists deltaSub deltaY : Real,
        highamCh4KahanSuffixCounterexampleLocalFacts fp.u
          (suffix.dropLast.get j) deltaSub deltaY := by
    intro j
    have hmemDropLast : suffix.dropLast.get j ∈ suffix.dropLast :=
      List.get_mem suffix.dropLast j
    have hmemSuffix : suffix.dropLast.get j ∈ suffix :=
      List.dropLast_subset suffix hmemDropLast
    have hmemSteps : suffix.dropLast.get j ∈ steps :=
      List.mem_of_mem_drop hmemSuffix
    exact
      kahanCoupledCoeffSteps_localFacts_of_mem
        fp v k hk hu1 hmemSteps
  have hlastMemSuffix : suffix.getLast hne ∈ suffix := List.getLast_mem hne
  have hlastMemSteps : suffix.getLast hne ∈ steps :=
    List.mem_of_mem_drop hlastMemSuffix
  have hA :
      |(suffix.getLast hne).returnedStateCoeff - 1| <= fp.u :=
    kahanCoupledCoeffSteps_returnedStateCoeff_abs_sub_one_le
      fp v k hk (suffix.getLast hne) hlastMemSteps
  have hB :
      |(suffix.getLast hne).returnedCorrectionCoeff| <= fp.u * (1 + fp.u) :=
    kahanCoupledCoeffSteps_returnedCorrectionCoeff_abs_le
      fp v k hk (suffix.getLast hne) hlastMemSteps
  have hret :=
    highamCh4KahanReturnedNonempty_majorant
      (u := fp.u) (steps := suffix)
      (init := KahanState.totalCorrection (steps.get i).sourceCoeff)
      hne fp.u_nonneg hu64 hm hprefixLocal hinitS hinitE hA hB
  have hsource :=
    kahanCoupledSourceCoeff_s_eq_returned_totalCorrectionPropagate steps i
  dsimp
  rw [hsource]
  simpa [steps, suffix] using hret

/-- Corrected ordinary returned source-coefficient bound for an empty suffix;
the source coefficient is just the local stored-sum input coefficient. -/
theorem kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_correctedReturnedMajorant_empty
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (k : Nat) (hk : k <= n)
    (i : Fin (kahanCoupledCoeffSteps fp v k hk).length)
    (hempty :
      ((kahanCoupledCoeffSteps fp v k hk).drop (i.val + 1)) = []) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    let suffix := steps.drop (i.val + 1)
    |(kahanCoupledSourceCoeff steps i).s - 1| <=
      3 * fp.u +
        ((9 + 13 * (suffix.dropLast.length : Real)) + 5) * fp.u ^ 2 +
          ((9 + 13 * (suffix.dropLast.length : Real)) + 3) * fp.u ^ 3 := by
  have hu0 := fp.u_nonneg
  have hB :
      |((kahanCoupledCoeffSteps fp v k hk).get i).B - 1| <=
        2 * fp.u + fp.u ^ 2 := by
    let steps := kahanCoupledCoeffSteps fp v k hk
    have hik : i.val < k := by
      simpa [steps, kahanCoupledCoeffSteps] using i.isLt
    let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le hik hk⟩
    have hget : steps.get i = kahanCoupledCoeffStepOfIndex fp v idx := by
      rw [List.get_eq_getElem]
      simp [steps, kahanCoupledCoeffSteps, idx]
    rw [hget]
    exact kahanCoupledCoeffStepOfIndex_B_abs_sub_one_le_two_u_plus_u_sq
      fp v idx
  have hsource :
      (kahanCoupledSourceCoeff (kahanCoupledCoeffSteps fp v k hk) i).s =
        ((kahanCoupledCoeffSteps fp v k hk).get i).B := by
    dsimp [kahanCoupledSourceCoeff, KahanCoupledCoeffStep.sourceCoeff,
      kahanCoupledCoeffPropagate]
    simp [hempty]
  dsimp
  rw [hsource]
  have hu3_nonneg : 0 <= fp.u ^ 3 := by positivity
  nlinarith [hB, hu0, sq_nonneg fp.u, hu3_nonneg]

/-- Corrected ordinary returned source-coefficient bound for actual Kahan
coefficient steps.  The leading constant is `3*u`, matching the whole-problem
source-statement audit for the ordinary returned coordinate rather than the
printed leading-`2*u` claim. -/
theorem kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_correctedReturnedMajorant
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (k : Nat) (hk : k <= n)
    (hu64 : fp.u <= 1 / 64)
    (i : Fin (kahanCoupledCoeffSteps fp v k hk).length)
    (hm :
      ((((kahanCoupledCoeffSteps fp v k hk).drop (i.val + 1)).dropLast.length : Real) *
          fp.u ^ 2 <= 1 / 16)) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    let suffix := steps.drop (i.val + 1)
    |(kahanCoupledSourceCoeff steps i).s - 1| <=
      3 * fp.u +
        ((9 + 13 * (suffix.dropLast.length : Real)) + 5) * fp.u ^ 2 +
          ((9 + 13 * (suffix.dropLast.length : Real)) + 3) * fp.u ^ 3 := by
  let steps := kahanCoupledCoeffSteps fp v k hk
  let suffix := steps.drop (i.val + 1)
  by_cases hnil : suffix = []
  · have hempty :
        ((kahanCoupledCoeffSteps fp v k hk).drop (i.val + 1)) = [] := by
      simpa [steps, suffix] using hnil
    simpa [steps, suffix] using
      kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_correctedReturnedMajorant_empty
        fp v k hk i hempty
  · have hne :
        Not (((kahanCoupledCoeffSteps fp v k hk).drop (i.val + 1)) = []) := by
      simpa [steps, suffix] using hnil
    simpa [steps, suffix] using
      kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_correctedReturnedMajorant_nonempty
        fp v k hk hu64 i hne hm

/-- Corrected ordinary returned-Kahan backward-error representation with
leading constant `3*u`.  This is source-honest for the current model after the
whole-problem audit: it does not claim Higham's printed ordinary returned
leading `2*u` statement, which remains available only in the conditional
exact-subtraction/coherence routes above. -/
theorem fl_kahanSum_backward_error_source_bound_correctedReturnedMajorant
    (fp : FPModel) (n : Nat) (v : Fin n -> Real)
    (hu64 : fp.u <= 1 / 64)
    (hm : (n : Real) * fp.u ^ 2 <= 1 / 16) :
    exists mu : Fin n -> Real,
      (forall i,
        |mu i| <=
          3 * fp.u + (14 + 13 * (n : Real)) * fp.u ^ 2 +
            (12 + 13 * (n : Real)) * fp.u ^ 3) /\
      fl_kahanSum fp n v = Finset.univ.sum (fun i : Fin n => v i * (1 + mu i)) := by
  let steps := kahanCoupledCoeffSteps fp v n (Nat.le_refl n)
  have hcoeff :
      forall i : Fin steps.length,
        |(kahanCoupledSourceCoeff steps i).s - 1| <=
          3 * fp.u + (14 + 13 * (n : Real)) * fp.u ^ 2 +
            (12 + 13 * (n : Real)) * fp.u ^ 3 := by
    intro i
    let suffix := steps.drop (i.val + 1)
    let m := suffix.dropLast.length
    have hm_le_n_nat : m <= n := by
      have hm_le_suffix : m <= suffix.length := by
        simp [m, List.length_dropLast]
      have hsuffix_le_steps : suffix.length <= steps.length := by
        dsimp [suffix]
        rw [List.length_drop]
        exact Nat.sub_le steps.length (i.val + 1)
      have hsteps_len : steps.length = n := by
        simp [steps, kahanCoupledCoeffSteps]
      have hm_le_steps : m <= steps.length := Nat.le_trans hm_le_suffix hsuffix_le_steps
      simpa [hsteps_len] using hm_le_steps
    have hm_le_n : (m : Real) <= (n : Real) := by exact_mod_cast hm_le_n_nat
    have hm_budget : (m : Real) * fp.u ^ 2 <= 1 / 16 := by
      have hu2_nonneg : 0 <= fp.u ^ 2 := sq_nonneg fp.u
      nlinarith [hm, hm_le_n, hu2_nonneg]
    have hsrc :=
      kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_correctedReturnedMajorant
        fp v n (Nat.le_refl n) hu64 i hm_budget
    have hbound :
        3 * fp.u +
              ((9 + 13 * (suffix.dropLast.length : Real)) + 5) *
                fp.u ^ 2 +
            ((9 + 13 * (suffix.dropLast.length : Real)) + 3) *
                fp.u ^ 3 <=
          3 * fp.u + (14 + 13 * (n : Real)) * fp.u ^ 2 +
            (12 + 13 * (n : Real)) * fp.u ^ 3 := by
      have hu2_nonneg : 0 <= fp.u ^ 2 := sq_nonneg fp.u
      have hu3_nonneg : 0 <= fp.u ^ 3 := by nlinarith [fp.u_nonneg, sq_nonneg fp.u]
      have hm_real : ((suffix.dropLast.length : Real)) <= (n : Real) := by
        simpa [m] using hm_le_n
      nlinarith
    dsimp [steps] at hsrc
    exact le_trans hsrc hbound
  exact
    fl_kahanSum_backward_error_source_bound_of_sourceCoeff_s_bound
      fp n v (by simpa [steps] using hcoeff)

theorem highamCh4KahanSuffixCounterexampleStep1_localFacts
    {u : Real} (hu0 : 0 <= u) (_hu1 : u <= 1) :
    highamCh4KahanSuffixCounterexampleLocalFacts u
      (highamCh4KahanSuffixCounterexampleStep1 u) (-u) u := by
  dsimp [highamCh4KahanSuffixCounterexampleLocalFacts,
    highamCh4KahanSuffixCounterexampleStep1,
    KahanCoupledCoeffStep.totalStateCoeff,
    KahanCoupledCoeffStep.totalInputCoeff,
    KahanCoupledCoeffStep.residualCoeff,
    KahanCoupledCoeffStep.correctionResidualCoeff]
  constructor
  · norm_num
    exact mul_nonneg (by norm_num : (0 : Real) <= 3) (sq_nonneg u)
  constructor
  · rw [abs_of_nonneg (by nlinarith [hu0, sq_nonneg u])]
    nlinarith [sq_nonneg u]
  constructor
  · norm_num
    exact mul_nonneg hu0 (sq_nonneg (1 + u))
  constructor
  · have hnonneg : 0 <= u * (1 + u) ^ 2 * (3 + u) := by
      exact mul_nonneg (mul_nonneg hu0 (sq_nonneg (1 + u))) (by nlinarith)
    rw [abs_of_nonneg (by nlinarith [hu0, sq_nonneg u])]
    ring_nf
    nlinarith [hu0, sq_nonneg u, hnonneg]
  constructor
  · rw [abs_of_nonneg (by ring_nf; exact sq_nonneg u)]
    ring_nf
    nlinarith [sq_nonneg u]
  constructor
  · ring_nf
    norm_num
    exact sq_nonneg u
  constructor
  · rw [abs_of_nonneg (by ring_nf; exact sq_nonneg u)]
    ring_nf
    nlinarith [sq_nonneg u]
  constructor
  · rw [abs_of_nonpos (by nlinarith : -u <= 0)]
    simp
  · rw [abs_of_nonneg hu0]

theorem highamCh4KahanSuffixCounterexampleStep2_localFacts
    {u : Real} (hu0 : 0 <= u) (_hu1 : u <= 1) :
    highamCh4KahanSuffixCounterexampleLocalFacts u
      (highamCh4KahanSuffixCounterexampleStep2 u) 0 0 := by
  dsimp [highamCh4KahanSuffixCounterexampleLocalFacts,
    highamCh4KahanSuffixCounterexampleStep2,
    KahanCoupledCoeffStep.totalStateCoeff,
    KahanCoupledCoeffStep.totalInputCoeff,
    KahanCoupledCoeffStep.residualCoeff,
    KahanCoupledCoeffStep.correctionResidualCoeff]
  constructor
  · norm_num
    nlinarith [sq_nonneg u]
  constructor
  · norm_num
    nlinarith [hu0, sq_nonneg u]
  constructor
  · rw [abs_of_nonpos (by nlinarith : -u <= 0)]
    have hone : 1 <= (1 + u) ^ 2 := by nlinarith [hu0, sq_nonneg u]
    calc
      -(-u) = u := by ring
      _ = u * 1 := by ring
      _ <= u * (1 + u) ^ 2 := mul_le_mul_of_nonneg_left hone hu0
  constructor
  · norm_num
    exact mul_nonneg (mul_nonneg hu0 (sq_nonneg (1 + u))) (by nlinarith)
  constructor
  · norm_num
    nlinarith [sq_nonneg u]
  constructor
  · ring_nf
    norm_num
    exact sq_nonneg u
  constructor
  · norm_num
    nlinarith [sq_nonneg u]
  constructor
  · norm_num
    exact hu0
  · norm_num
    exact hu0

/-- Exact returned-coefficient error in the two-step symbolic suffix
counterexample. -/
theorem highamCh4KahanSuffixCounterexampleReturnedCoeff_abs_sub_one_eq
    {u : Real} (hu0 : 0 <= u) :
    |highamCh4KahanSuffixCounterexampleReturnedCoeff u - 1| =
      3 * u + 3 * u ^ 2 + u ^ 3 := by
  rw [highamCh4KahanSuffixCounterexampleReturnedCoeff_eq]
  have hpoly_nonneg : 0 <= 3 * u + 3 * u ^ 2 + u ^ 3 := by
    nlinarith [hu0, sq_nonneg u, mul_nonneg (sq_nonneg u) hu0]
  rw [show (1 + u) ^ 3 - 1 = 3 * u + 3 * u ^ 2 + u ^ 3 by ring]
  exact abs_of_nonneg hpoly_nonneg

/-- On the usual small-unit interval, the symbolic suffix counterexample has a
leading-`3*u` returned-coefficient error.  This is a route audit for corrected
surfaces; it is not a positive theorem for arbitrary Kahan traces. -/
theorem highamCh4KahanSuffixCounterexampleReturnedCoeff_abs_sub_one_le_three_u_plus_four_u_sq
    {u : Real} (hu0 : 0 <= u) (hu1 : u <= 1) :
    |highamCh4KahanSuffixCounterexampleReturnedCoeff u - 1| <=
      3 * u + 4 * u ^ 2 := by
  rw [highamCh4KahanSuffixCounterexampleReturnedCoeff_abs_sub_one_eq hu0]
  nlinarith [hu0, hu1, sq_nonneg u, mul_nonneg (sq_nonneg u) hu0]

/-- The local suffix-recurrence facts alone cannot imply a
`2*u + K*u^2` returned-coefficient cap with any fixed nonnegative constant
`K`.  The counterexample is purely algebraic; it is a route audit, not a claim
that the two symbolic steps are realized by round-to-even arithmetic. -/
theorem highamCh4KahanSuffixCounterexample_not_two_u_plus_K_u_sq
    (K u : Real) (hK : 0 <= K) (hu : 0 < u)
    (huSmall : u < min (1 / 20) (1 / (K + 1))) :
    highamCh4KahanSuffixCounterexampleLocalFacts u
      (highamCh4KahanSuffixCounterexampleStep1 u) (-u) u ∧
    highamCh4KahanSuffixCounterexampleLocalFacts u
      (highamCh4KahanSuffixCounterexampleStep2 u) 0 0 ∧
    2 * u + K * u ^ 2 <
      |highamCh4KahanSuffixCounterexampleReturnedCoeff u - 1| := by
  have hu0 : 0 <= u := le_of_lt hu
  have hu_lt_one_twentieth : u < 1 / 20 := lt_of_lt_of_le huSmall (min_le_left _ _)
  have hu1 : u <= 1 := by nlinarith
  have hK1pos : 0 < K + 1 := by nlinarith
  have hu_lt_inv : u < 1 / (K + 1) := lt_of_lt_of_le huSmall (min_le_right _ _)
  have hmul : u * (K + 1) < 1 := by
    rw [lt_div_iff₀ hK1pos] at hu_lt_inv
    simpa [mul_comm] using hu_lt_inv
  have hKu : K * u < 1 := by nlinarith
  have hKu2 : K * u ^ 2 < u := by nlinarith [mul_pos hK1pos hu, hKu]
  have hret :
      |highamCh4KahanSuffixCounterexampleReturnedCoeff u - 1| =
        3 * u + 3 * u ^ 2 + u ^ 3 := by
    exact highamCh4KahanSuffixCounterexampleReturnedCoeff_abs_sub_one_eq hu0
  refine ⟨?_, ?_, ?_⟩
  · exact highamCh4KahanSuffixCounterexampleStep1_localFacts hu0 hu1
  · exact highamCh4KahanSuffixCounterexampleStep2_localFacts hu0 hu1
  · rw [hret]
    nlinarith [hKu2, sq_nonneg u, mul_nonneg (sq_nonneg u) hu0]

/-- For the concrete p=5 scale (`p = 32`, so `2u = 1/16`), the returned
four-term finite round-to-even trace cannot be represented with all source
weights bounded by `2u`. -/
theorem highamCh4KahanReturnedCounterexampleP5_no_source_bound_one_sixteenth
    (fmt : FloatingPointFormat)
    (hround : HighamCh4KahanReturnedCounterexampleRounding fmt 32) :
    Not (Exists fun
      (mu : HighamCh4KahanReturnedCounterexampleWeight) =>
        highamCh4KahanReturnedCounterexampleSourceRepresentation
          fmt 32 (1 / 16) mu) := by
  intro h
  cases h with
  | intro mu hrep =>
      cases hrep with
      | intro hmu hsum =>
          have hp32 : (1 : Real) <= 32 := by norm_num
          have hbound :=
            highamCh4KahanReturnedCounterexample_productLowerBound
              fmt hp32 hround mu hmu hsum
          norm_num at hbound

/-- The concrete p=5 binary finite round-to-even trace finishes at stored sum
`-352` with retained correction `8`. -/
theorem highamCh4KahanReturnedCounterexampleP5_state_eq :
    finiteKahanState highamCh4KahanReturnedCounterexampleP5Format 4
        (highamCh4KahanReturnedCounterexampleInput 32) =
      { s := highamCh4KahanReturnedCounterexampleS3 32,
        e := highamCh4KahanReturnedCounterexampleX4 } :=
  highamCh4KahanReturnedCounterexampleState_eq_of_rounding
    highamCh4KahanReturnedCounterexampleP5Format
    highamCh4KahanReturnedCounterexampleP5_rounding

/-- Concrete p=5 finite round-to-even Kahan counterexample: no source-weight
representation with all coefficients bounded by `1/16` can produce the returned
stored sum. -/
theorem highamCh4KahanReturnedCounterexampleP5_no_source_bound_one_sixteenth_actual :
    Not (Exists fun
      (mu : HighamCh4KahanReturnedCounterexampleWeight) =>
        highamCh4KahanReturnedCounterexampleSourceRepresentation
          highamCh4KahanReturnedCounterexampleP5Format 32 (1 / 16) mu) :=
  highamCh4KahanReturnedCounterexampleP5_no_source_bound_one_sixteenth
    highamCh4KahanReturnedCounterexampleP5Format
    highamCh4KahanReturnedCounterexampleP5_rounding

/-- The tail-order FastTwoSum hypothesis is a genuine extra hypothesis, not a
consequence of the finite Kahan trace for arbitrary input order.

For the two-term input `[1, 2]`, the second correction-formula call has
`temp = 1` and `y = 2`, so `|y| < |temp|` is false. -/
theorem not_forall_finiteKahanTrace_tail_abs_order
    (fmt : FloatingPointFormat)
    (hone : fmt.finiteSystem (1 : ℝ))
    (htwo : fmt.finiteSystem (2 : ℝ)) :
    let v : Fin 2 → ℝ := fun i => if i.val = 0 then 1 else 2
    ¬ (∀ i : Fin 2, i.val ≠ 0 →
        |(finiteKahanTrace fmt v i).y| <
          |(finiteKahanTrace fmt v i).temp|) := by
  intro v horder
  let i : Fin 2 := ⟨1, by norm_num⟩
  have hv0 : fmt.finiteSystem (v ⟨0, by norm_num⟩) := by
    simpa [v] using hone
  have hprefix :
      finiteKahanPrefixState fmt v 1 (by norm_num : 1 ≤ 2) =
        { s := 1, e := 0 } := by
    simpa [v] using
      finiteKahanPrefixState_one_of_finiteSystem
        fmt v (by norm_num : 1 ≤ 2) hv0
  have hyround :
      fmt.finiteRoundToEvenOp BasicOp.add (2 : ℝ) 0 = 2 :=
    fmt.finiteRoundToEvenOp_add_zero_right_of_finiteSystem htwo
  have hprefix_e :
      (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt)).e = 0 := by
    simp [i, hprefix]
  have htemp : (finiteKahanTrace fmt v i).temp = 1 := by
    simp [finiteKahanTrace, finiteKahanStepTrace, i, hprefix]
  have hy : (finiteKahanTrace fmt v i).y = 2 := by
    have hinput : v i = 2 := by
      simp [i, v]
    calc
      (finiteKahanTrace fmt v i).y =
          fmt.finiteRoundToEvenOp BasicOp.add (v i)
            (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt)).e := by
            rfl
      _ = fmt.finiteRoundToEvenOp BasicOp.add 2 0 := by
            rw [hinput, hprefix_e]
      _ = 2 := hyround
  have hbad := horder i (by norm_num : i.val ≠ 0)
  rw [hy, htemp] at hbad
  norm_num at hbad

/-- The tail-only inclusive Sterbenz route is also not a consequence of the
finite Kahan trace for arbitrary input order.

For the two-term input `[1, 2]` with exact representability of `1`, `2`, and
`3`, the second correction-subtraction pair has `temp = 1` and rounded
`s = 3`, so the inclusive Sterbenz condition `s / 2 <= temp` is false. -/
theorem not_forall_finiteKahanTrace_tail_sterbenzLe
    (fmt : FloatingPointFormat)
    (hone : fmt.finiteSystem (1 : ℝ))
    (htwo : fmt.finiteSystem (2 : ℝ))
    (hthree : fmt.finiteSystem (3 : ℝ)) :
    let v : Fin 2 → ℝ := fun i => if i.val = 0 then 1 else 2
    ¬ (∀ i : Fin 2, i.val ≠ 0 →
        fmt.sterbenzRatioConditionLe
          (finiteKahanTrace fmt v i).temp
          (finiteKahanTrace fmt v i).s) := by
  intro v hsterbenz
  let i : Fin 2 := ⟨1, by norm_num⟩
  have hv0 : fmt.finiteSystem (v ⟨0, by norm_num⟩) := by
    simpa [v] using hone
  have hprefix :
      finiteKahanPrefixState fmt v 1 (by norm_num : 1 ≤ 2) =
        { s := 1, e := 0 } := by
    simpa [v] using
      finiteKahanPrefixState_one_of_finiteSystem
        fmt v (by norm_num : 1 ≤ 2) hv0
  have hprefix_e :
      (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt)).e = 0 := by
    simp [i, hprefix]
  have htemp : (finiteKahanTrace fmt v i).temp = 1 := by
    simp [finiteKahanTrace, finiteKahanStepTrace, i, hprefix]
  have hy : (finiteKahanTrace fmt v i).y = 2 := by
    have hinput : v i = 2 := by
      simp [i, v]
    have hyround :
        fmt.finiteRoundToEvenOp BasicOp.add (2 : ℝ) 0 = 2 :=
      fmt.finiteRoundToEvenOp_add_zero_right_of_finiteSystem htwo
    calc
      (finiteKahanTrace fmt v i).y =
          fmt.finiteRoundToEvenOp BasicOp.add (v i)
            (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt)).e := by
            rfl
      _ = fmt.finiteRoundToEvenOp BasicOp.add 2 0 := by
            rw [hinput, hprefix_e]
      _ = 2 := hyround
  have hs : (finiteKahanTrace fmt v i).s = 3 := by
    have hthreeExact :
        fmt.finiteSystem (BasicOp.exact BasicOp.add (1 : ℝ) 2) := by
      convert hthree using 1
      norm_num [BasicOp.exact]
    have hsround :
        fmt.finiteRoundToEvenOp BasicOp.add (1 : ℝ) 2 = 3 := by
      have hround :=
        (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
          (op := BasicOp.add) (x := (1 : ℝ)) (y := (2 : ℝ)) hthreeExact)
      norm_num [BasicOp.exact] at hround
      exact hround
    calc
      (finiteKahanTrace fmt v i).s =
          fmt.finiteRoundToEvenOp BasicOp.add
            (finiteKahanTrace fmt v i).temp
            (finiteKahanTrace fmt v i).y := by
            rfl
      _ = fmt.finiteRoundToEvenOp BasicOp.add (1 : ℝ) 2 := by
            rw [htemp, hy]
      _ = 3 := hsround
  have hbad := hsterbenz i (by norm_num : i.val ≠ 0)
  rw [htemp, hs] at hbad
  norm_num [FloatingPointFormat.sterbenzRatioConditionLe] at hbad

/-- The tail-only inclusive Ferguson route is not a consequence of the finite
Kahan trace for arbitrary input order.

For the all-zero two-term input, the nonzero tail index still has `temp = 0`
and `s = 0`; Ferguson's condition requires normalized operands, so it fails. -/
theorem not_forall_finiteKahanTrace_tail_fergusonLe
    (fmt : FloatingPointFormat) :
    let v : Fin 2 → ℝ := fun _ => 0
    ¬ (∀ i : Fin 2, i.val ≠ 0 →
        fmt.fergusonExponentConditionLe
          (finiteKahanTrace fmt v i).temp
          (finiteKahanTrace fmt v i).s) := by
  intro v hferguson
  let i : Fin 2 := ⟨1, by norm_num⟩
  have hv0 : fmt.finiteSystem (v ⟨0, by norm_num⟩) := by
    simp [v, fmt.finiteSystem_zero]
  have hprefix :
      finiteKahanPrefixState fmt v 1 (by norm_num : 1 ≤ 2) =
        { s := 0, e := 0 } := by
    simpa [v] using
      finiteKahanPrefixState_one_of_finiteSystem
        fmt v (by norm_num : 1 ≤ 2) hv0
  have htemp : (finiteKahanTrace fmt v i).temp = 0 := by
    simp [finiteKahanTrace, finiteKahanStepTrace, i, hprefix]
  have hs : (finiteKahanTrace fmt v i).s = 0 := by
    have hprefix_e :
        (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt)).e = 0 := by
      simp [i, hprefix]
    have hinput : v i = 0 := by
      simp [v]
    have hy : (finiteKahanTrace fmt v i).y = 0 := by
      calc
        (finiteKahanTrace fmt v i).y =
            fmt.finiteRoundToEvenOp BasicOp.add (v i)
              (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt)).e := by
              rfl
        _ = fmt.finiteRoundToEvenOp BasicOp.add 0 0 := by
              rw [hinput, hprefix_e]
        _ = 0 := fmt.finiteRoundToEvenOp_add_zero_of_finiteSystem fmt.finiteSystem_zero
    calc
      (finiteKahanTrace fmt v i).s =
          fmt.finiteRoundToEvenOp BasicOp.add
            (finiteKahanTrace fmt v i).temp
            (finiteKahanTrace fmt v i).y := by
            rfl
      _ = fmt.finiteRoundToEvenOp BasicOp.add 0 0 := by
            rw [htemp, hy]
      _ = 0 := fmt.finiteRoundToEvenOp_add_zero_of_finiteSystem fmt.finiteSystem_zero
  have hbad := hferguson i (by norm_num : i.val ≠ 0)
  have hleft : fmt.normalizedSystem (finiteKahanTrace fmt v i).temp :=
    fmt.fergusonExponentConditionLe_left_normalized hbad
  rw [htemp] at hleft
  have hzeroLower : fmt.betaR ^ (fmt.emin - 1) ≤ (0 : ℝ) := by
    simpa using fmt.normalizedSystem_abs_lower_bound hleft
  exact (not_lt_of_ge hzeroLower) (fmt.betaR_zpow_pos (fmt.emin - 1))

/-- Direct tail finite representability of `temp - s` is not a consequence of
the finite Kahan trace for arbitrary input order.

In the two-exponent one-digit decimal audit format, the input `[1, 90]` has tail
`temp = 1` and saturated rounded sum `s = 90`, so `temp - s = -89`, which is not
finite representable. -/
theorem not_forall_finiteKahanTrace_tail_direct_sub_finite :
    let fmt := FloatingPointFormat.decimalSingleDigitTwoExponentFormat
    let v : Fin 2 → ℝ := fun i => if i.val = 0 then 1 else 90
    ¬ (∀ i : Fin 2, i.val ≠ 0 →
        fmt.finiteSystem
          ((finiteKahanTrace fmt v i).temp -
            (finiteKahanTrace fmt v i).s)) := by
  intro fmt v hfinite
  let i : Fin 2 := ⟨1, by norm_num⟩
  have hv0 : fmt.finiteSystem (v ⟨0, by norm_num⟩) := by
    simpa [v, fmt] using
      FloatingPointFormat.decimalSingleDigitTwoExponentFormat_finiteSystem_one
  have hprefix :
      finiteKahanPrefixState fmt v 1 (by norm_num : 1 ≤ 2) =
        { s := 1, e := 0 } := by
    simpa [v, fmt] using
      finiteKahanPrefixState_one_of_finiteSystem
        fmt v (by norm_num : 1 ≤ 2) hv0
  have hprefix_e :
      (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt)).e = 0 := by
    simp [i, hprefix]
  have htemp : (finiteKahanTrace fmt v i).temp = 1 := by
    simp [finiteKahanTrace, finiteKahanStepTrace, i, hprefix]
  have hy : (finiteKahanTrace fmt v i).y = 90 := by
    have hinput : v i = 90 := by
      simp [i, v]
    have hround :
        fmt.finiteRoundToEvenOp BasicOp.add (90 : ℝ) 0 = 90 := by
      simpa [fmt] using
        fmt.finiteRoundToEvenOp_add_zero_right_of_finiteSystem
          FloatingPointFormat.decimalSingleDigitTwoExponentFormat_finiteSystem_ninety
    calc
      (finiteKahanTrace fmt v i).y =
          fmt.finiteRoundToEvenOp BasicOp.add (v i)
            (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt)).e := by
            rfl
      _ = fmt.finiteRoundToEvenOp BasicOp.add 90 0 := by
            rw [hinput, hprefix_e]
      _ = 90 := hround
  have hs : (finiteKahanTrace fmt v i).s = 90 := by
    calc
      (finiteKahanTrace fmt v i).s =
          fmt.finiteRoundToEvenOp BasicOp.add
            (finiteKahanTrace fmt v i).temp
            (finiteKahanTrace fmt v i).y := by
            rfl
      _ = fmt.finiteRoundToEvenOp BasicOp.add (1 : ℝ) 90 := by
            rw [htemp, hy]
      _ = 90 := by
            simpa [fmt] using
              FloatingPointFormat.decimalSingleDigitTwoExponentFormat_round_add_one_ninety
  have hbad := hfinite i (by norm_num : i.val ≠ 0)
  rw [htemp, hs] at hbad
  norm_num at hbad
  have hpos :
      FloatingPointFormat.decimalSingleDigitTwoExponentFormat.finiteSystem (89 : ℝ) := by
    simpa [fmt] using
      FloatingPointFormat.decimalSingleDigitTwoExponentFormat.finiteSystem_neg hbad
  exact FloatingPointFormat.decimalSingleDigitTwoExponentFormat_not_finiteSystem_eightynine hpos

/-- Concrete value of the tail correction subtraction in the direct finite
subtraction route counterexample. -/
theorem finiteKahanTrace_decimal_tail_direct_sub_eq_neg_eightynine :
    let fmt := FloatingPointFormat.decimalSingleDigitTwoExponentFormat
    let v : Fin 2 → ℝ := fun i => if i.val = 0 then 1 else 90
    let i : Fin 2 := ⟨1, by norm_num⟩
    (finiteKahanTrace fmt v i).temp -
        (finiteKahanTrace fmt v i).s = -89 := by
  dsimp
  let fmt := FloatingPointFormat.decimalSingleDigitTwoExponentFormat
  let v : Fin 2 → ℝ := fun i => if i.val = 0 then 1 else 90
  let i : Fin 2 := ⟨1, by norm_num⟩
  have hv0 : fmt.finiteSystem (v ⟨0, by norm_num⟩) := by
    simpa [v, fmt] using
      FloatingPointFormat.decimalSingleDigitTwoExponentFormat_finiteSystem_one
  have hprefix :
      finiteKahanPrefixState fmt v 1 (by norm_num : 1 ≤ 2) =
        { s := 1, e := 0 } := by
    simpa [v, fmt] using
      finiteKahanPrefixState_one_of_finiteSystem
        fmt v (by norm_num : 1 ≤ 2) hv0
  have hprefix_e :
      (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt)).e = 0 := by
    simp [i, hprefix]
  have htemp : (finiteKahanTrace fmt v i).temp = 1 := by
    simp [finiteKahanTrace, finiteKahanStepTrace, i, hprefix]
  have hy : (finiteKahanTrace fmt v i).y = 90 := by
    have hinput : v i = 90 := by
      simp [i, v]
    have hround :
        fmt.finiteRoundToEvenOp BasicOp.add (90 : ℝ) 0 = 90 := by
      simpa [fmt] using
        fmt.finiteRoundToEvenOp_add_zero_right_of_finiteSystem
          FloatingPointFormat.decimalSingleDigitTwoExponentFormat_finiteSystem_ninety
    calc
      (finiteKahanTrace fmt v i).y =
          fmt.finiteRoundToEvenOp BasicOp.add (v i)
            (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt)).e := by
            rfl
      _ = fmt.finiteRoundToEvenOp BasicOp.add 90 0 := by
            rw [hinput, hprefix_e]
      _ = 90 := hround
  have hs : (finiteKahanTrace fmt v i).s = 90 := by
    calc
      (finiteKahanTrace fmt v i).s =
          fmt.finiteRoundToEvenOp BasicOp.add
            (finiteKahanTrace fmt v i).temp
            (finiteKahanTrace fmt v i).y := by
            rfl
      _ = fmt.finiteRoundToEvenOp BasicOp.add (1 : ℝ) 90 := by
            rw [htemp, hy]
      _ = 90 := by
            simpa [fmt] using
              FloatingPointFormat.decimalSingleDigitTwoExponentFormat_round_add_one_ninety
  have hsub :
      (finiteKahanTrace fmt v i).temp -
          (finiteKahanTrace fmt v i).s = -89 := by
    rw [htemp, hs]
    norm_num
  simpa [fmt, v, i] using hsub

/-- The source-facing finite-normal-range shortcut does not repair the failed
direct finite-subtraction route for arbitrary Kahan input order.

In the same two-exponent one-digit decimal audit trace used by
`not_forall_finiteKahanTrace_tail_direct_sub_finite`, the tail correction
subtraction is `-89`.  Its magnitude lies in the finite normal range, but the
value is not representable in the finite system.  Thus a no-overflow/range
hypothesis alone is weaker than the finite/coherence hypothesis needed by
`fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sub_finite`. -/
theorem finiteKahanTrace_tail_direct_sub_finiteNormalRange_not_finiteSystem_counterexample :
    let fmt := FloatingPointFormat.decimalSingleDigitTwoExponentFormat
    let v : Fin 2 → ℝ := fun i => if i.val = 0 then 1 else 90
    (∀ i : Fin 2, i.val ≠ 0 →
        fmt.finiteNormalRange
          ((finiteKahanTrace fmt v i).temp -
            (finiteKahanTrace fmt v i).s)) ∧
      ¬ (∀ i : Fin 2, i.val ≠ 0 →
        fmt.finiteSystem
          ((finiteKahanTrace fmt v i).temp -
            (finiteKahanTrace fmt v i).s)) := by
  dsimp
  constructor
  · intro i hi
    fin_cases i
    · exact False.elim (hi rfl)
    · have hsub := finiteKahanTrace_decimal_tail_direct_sub_eq_neg_eightynine
      dsimp at hsub
      have hnormal :
          FloatingPointFormat.decimalSingleDigitTwoExponentFormat.finiteNormalRange
            (-89 : ℝ) := by
        rw [FloatingPointFormat.finiteNormalRange]
        have hmin :
            FloatingPointFormat.decimalSingleDigitTwoExponentFormat.minNormalMagnitude =
              (1 : ℝ) := by
          norm_num [FloatingPointFormat.minNormalMagnitude,
            FloatingPointFormat.decimalSingleDigitTwoExponentFormat,
            FloatingPointFormat.betaR]
        have hmax :
            FloatingPointFormat.decimalSingleDigitTwoExponentFormat.maxFiniteMagnitude =
              (90 : ℝ) := by
          norm_num [FloatingPointFormat.maxFiniteMagnitude,
            FloatingPointFormat.decimalSingleDigitTwoExponentFormat,
            FloatingPointFormat.betaR, zpow_neg]
          rfl
        constructor
        · rw [hmin]
          norm_num
        · rw [hmax]
          norm_num
      have htarget :
          FloatingPointFormat.decimalSingleDigitTwoExponentFormat.finiteNormalRange
            ((finiteKahanTrace
                FloatingPointFormat.decimalSingleDigitTwoExponentFormat
                (fun i : Fin 2 => if i.val = 0 then 1 else 90)
                (⟨1, by norm_num⟩ : Fin 2)).temp -
              (finiteKahanTrace
                FloatingPointFormat.decimalSingleDigitTwoExponentFormat
                (fun i : Fin 2 => if i.val = 0 then 1 else 90)
                (⟨1, by norm_num⟩ : Fin 2)).s) := by
        have hsub' :
            (finiteKahanTrace
                  FloatingPointFormat.decimalSingleDigitTwoExponentFormat
                  (fun i : Fin 2 => if i.val = 0 then 1 else 90)
                  (⟨1, by norm_num⟩ : Fin 2)).temp -
                (finiteKahanTrace
                  FloatingPointFormat.decimalSingleDigitTwoExponentFormat
                  (fun i : Fin 2 => if i.val = 0 then 1 else 90)
                  (⟨1, by norm_num⟩ : Fin 2)).s =
              -89 := by
          simpa using hsub
        rw [hsub']
        exact hnormal
      simpa using htarget
  · simpa using not_forall_finiteKahanTrace_tail_direct_sub_finite

/-- Source-shaped backward-error representation for the compensated total
`s+e` retained by Algorithm 4.2.

This closes the paired-total Goldberg/Knuth coefficient route with an explicit
loose `2*u + O(n*u^2)` bound.  It is an intermediate theorem for the
compensated total, not the still-open Higham equation (4.8) theorem for the
ordinary returned value `fl_kahanSum`. -/
theorem fl_kahanCompensatedTotal_backward_error_source_bound
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (9 + 200 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ 2 * fp.u + (9 + 200 * (n : ℝ)) * fp.u ^ 2) ∧
      (fl_kahanState fp n v).s + (fl_kahanState fp n v).e =
        ∑ i : Fin n, v i * (1 + μ i) := by
  let steps := kahanCoupledCoeffSteps fp v n (Nat.le_refl n)
  have hlen : n = steps.length := by
    simp [steps, kahanCoupledCoeffSteps]
  let idx : Fin n → Fin steps.length := fun i => finCongr hlen i
  let μ : Fin n → ℝ := fun i => kahanCoupledSourceTotalCoeff steps (idx i) - 1
  refine ⟨μ, ?_, ?_⟩
  · intro i
    dsimp [μ]
    have hdrop_nat :
        (steps.drop ((idx i).val + 1)).length ≤ steps.length := by
      rw [List.length_drop]
      exact Nat.sub_le steps.length ((idx i).val + 1)
    have hdrop_le :
        ((steps.drop ((idx i).val + 1)).length : ℝ) ≤ (n : ℝ) := by
      have hdrop_le_steps :
          ((steps.drop ((idx i).val + 1)).length : ℝ) ≤
            (steps.length : ℝ) := by
        exact_mod_cast hdrop_nat
      simpa [hlen] using hdrop_le_steps
    have hbudget_i :
        (9 + 200 * ((steps.drop ((idx i).val + 1)).length : ℝ)) *
            fp.u ≤ 1 := by
      have hcoef :
          9 + 200 * ((steps.drop ((idx i).val + 1)).length : ℝ) ≤
            9 + 200 * (n : ℝ) := by nlinarith
      have hmul := mul_le_mul_of_nonneg_right hcoef fp.u_nonneg
      nlinarith
    have hcoeff :=
      kahanCoupledCoeffSteps_sourceTotalCoeff_abs_sub_one_le_two_u_plus_majorant
        fp v n (Nat.le_refl n) huSmall (idx i)
        (by simpa [steps] using hbudget_i)
    have htarget :
        |kahanCoupledSourceTotalCoeff steps (idx i) - 1| ≤
          2 * fp.u +
            (9 + 200 * ((steps.drop ((idx i).val + 1)).length : ℝ)) *
              fp.u ^ 2 := by
      simpa [steps] using hcoeff
    have hcoef2 :
        (9 + 200 * ((steps.drop ((idx i).val + 1)).length : ℝ)) *
            fp.u ^ 2 ≤
          (9 + 200 * (n : ℝ)) * fp.u ^ 2 := by
      have hcoef :
          9 + 200 * ((steps.drop ((idx i).val + 1)).length : ℝ) ≤
            9 + 200 * (n : ℝ) := by nlinarith
      exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg fp.u)
    nlinarith
  · have htotal :=
      kahanCoupledCoeffSteps_prefixState_total_eq_sum_sourceTotalCoeff
        fp v n (Nat.le_refl n)
    have hsum :
        (∑ i : Fin n, v i * (1 + μ i)) =
          ∑ j : Fin steps.length,
            (steps.get j).x * kahanCoupledSourceTotalCoeff steps j := by
      refine Fintype.sum_equiv (finCongr hlen) _ _ ?_
      intro i
      dsimp [μ, idx]
      simp [steps, kahanCoupledCoeffSteps, kahanCoupledCoeffStepOfIndex]
    simpa [fl_kahanState, steps] using htotal.trans hsum.symm

/-- Prefix invariant for Algorithm 4.2 from exact local correction.

If every processed Kahan step has exact `y = x + e` and its equation-(4.7)
local correction formula is exact, then the compensated total `s + e` after
the first `k` steps is the exact sum of the first `k` source inputs.  This is
the loop-level algebraic bridge from the local correction formula to Kahan's
persistent compensated state; it does not instantiate the cited backward-error
constants from Higham equations (4.8)--(4.9). -/
theorem kahanPrefixState_compensated_total_eq_sum_of_exact_steps
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      (∀ i : Fin k,
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        let state :=
          kahanPrefixState fp v i.val
            (Nat.le_trans (Nat.le_of_lt i.isLt) hk)
        let trace := kahanStepTrace fp (v idx) state
        trace.y = v idx + state.e ∧
          CorrectionFormulaTrace.exact state.s trace.y
            ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace)) →
      (kahanPrefixState fp v k hk).s +
          (kahanPrefixState fp v k hk).e =
        ∑ i : Fin k, v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  | 0, hk, _hexact => by
      simp [kahanPrefixState, KahanState.zero]
  | k + 1, hk, hexact => by
      have hprev_le : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let prev := kahanPrefixState fp v k hprev_le
      let idx : Fin n :=
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let trace := kahanStepTrace fp (v idx) prev
      have hfold :
          kahanPrefixState fp v (k + 1) hk =
            kahanStep fp (v idx) prev := by
        unfold kahanPrefixState
        rw [Fin.foldl_succ_last]
        rfl
      have hprev :
          prev.s + prev.e =
            ∑ i : Fin k, v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hprev_le⟩ := by
        apply kahanPrefixState_compensated_total_eq_sum_of_exact_steps fp v
        intro i
        simpa [prev, idx, trace] using hexact i.castSucc
      have hlocal := hexact (Fin.last k)
      have hstep :
          (kahanStep fp (v idx) prev).s +
              (kahanStep fp (v idx) prev).e =
            prev.s + v idx + prev.e := by
        exact kahanStep_compensated_total_eq_of_exact_y_and_correction
          fp (v idx) prev hlocal.1 hlocal.2
      rw [hfold, hstep]
      calc
        prev.s + v idx + prev.e = (prev.s + prev.e) + v idx := by ring
        _ = (∑ i : Fin k,
              v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hprev_le⟩) + v idx := by
            rw [hprev]
        _ = ∑ i : Fin (k + 1),
              v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ := by
            rw [Fin.sum_univ_castSucc]
            rfl

/-- Full-state form of
`kahanPrefixState_compensated_total_eq_sum_of_exact_steps`. -/
theorem fl_kahanState_compensated_total_eq_sum_of_exact_steps
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
        let trace := kahanStepTrace fp (v i) state
        trace.y = v i + state.e ∧
          CorrectionFormulaTrace.exact state.s trace.y
            ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace)) :
    (fl_kahanState fp n v).s + (fl_kahanState fp n v).e =
      ∑ i : Fin n, v i := by
  simpa [fl_kahanState] using
    kahanPrefixState_compensated_total_eq_sum_of_exact_steps
      fp v n (Nat.le_refl n) hexact

/-- Public returned-sum/correction form of the exact-step Kahan invariant. -/
theorem fl_kahanSum_add_correction_eq_sum_of_exact_steps
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
        let trace := kahanStepTrace fp (v i) state
        trace.y = v i + state.e ∧
          CorrectionFormulaTrace.exact state.s trace.y
            ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace)) :
    fl_kahanSum fp n v + fl_kahanCorrection fp n v =
      ∑ i : Fin n, v i := by
  simpa [fl_kahanSum, fl_kahanCorrection] using
    fl_kahanState_compensated_total_eq_sum_of_exact_steps fp n v hexact

/-- Final-correction variant described on p. 93: append `s = s + e` after
Algorithm 4.2. -/
noncomputable def fl_kahanFinalCorrectedSum (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  fp.fl_add (fl_kahanSum fp n v) (fl_kahanCorrection fp n v)

/-- The p. 93 appended final correction is the rounded add of final `s` and
final `e`. -/
theorem fl_kahanFinalCorrectedSum_eq_add_correction (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) :
    fl_kahanFinalCorrectedSum fp n v =
      fp.fl_add (fl_kahanSum fp n v) (fl_kahanCorrection fp n v) := by
  rfl

/-- If every Kahan step satisfies the exact local correction hypotheses and
the appended final correction add is exact, the final-corrected variant
returns the exact source sum. -/
theorem fl_kahanFinalCorrectedSum_eq_sum_of_exact_steps_and_final_add
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
        let trace := kahanStepTrace fp (v i) state
        trace.y = v i + state.e ∧
          CorrectionFormulaTrace.exact state.s trace.y
            ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hfinal :
      fp.fl_add (fl_kahanSum fp n v) (fl_kahanCorrection fp n v) =
        fl_kahanSum fp n v + fl_kahanCorrection fp n v) :
    fl_kahanFinalCorrectedSum fp n v = ∑ i : Fin n, v i := by
  rw [fl_kahanFinalCorrectedSum_eq_add_correction, hfinal]
  exact fl_kahanSum_add_correction_eq_sum_of_exact_steps fp n v hexact

/-- Under exact arithmetic, Kahan's state after all inputs have been processed
is the exact source sum with zero retained correction. -/
theorem fl_kahanState_exactWithUnitRoundoff (u0 : ℝ) (hu0 : 0 ≤ u0) :
    ∀ (n : ℕ) (v : Fin n → ℝ),
      fl_kahanState (FPModel.exactWithUnitRoundoff u0 hu0) n v =
        { s := ∑ i : Fin n, v i, e := 0 }
  | 0, _v => by
      simp [fl_kahanState, kahanPrefixState, KahanState.zero]
  | n + 1, v => by
      let fp := FPModel.exactWithUnitRoundoff u0 hu0
      have hfold :
          fl_kahanState fp (n + 1) v =
            kahanStep fp (v (Fin.last n))
              (fl_kahanState fp n (fun i : Fin n => v i.castSucc)) := by
        unfold fl_kahanState kahanPrefixState
        rw [Fin.foldl_succ_last]
      rw [hfold, fl_kahanState_exactWithUnitRoundoff u0 hu0 n
        (fun i : Fin n => v i.castSucc)]
      simp [fp, kahanStep, kahanStepTrace, KahanStepTrace.nextState,
        FPModel.exactWithUnitRoundoff, Fin.sum_univ_castSucc,
        add_comm]

/-- Under exact arithmetic, Kahan's returned sum is the exact source sum. -/
theorem fl_kahanSum_exactWithUnitRoundoff (u0 : ℝ) (hu0 : 0 ≤ u0)
    (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanSum (FPModel.exactWithUnitRoundoff u0 hu0) n v =
      ∑ i : Fin n, v i := by
  have hstate := fl_kahanState_exactWithUnitRoundoff u0 hu0 n v
  simpa [fl_kahanSum] using congrArg KahanState.s hstate

/-- Under exact arithmetic, Kahan's retained correction is zero. -/
theorem fl_kahanCorrection_exactWithUnitRoundoff (u0 : ℝ) (hu0 : 0 ≤ u0)
    (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanCorrection (FPModel.exactWithUnitRoundoff u0 hu0) n v = 0 := by
  have hstate := fl_kahanState_exactWithUnitRoundoff u0 hu0 n v
  simpa [fl_kahanCorrection] using congrArg KahanState.e hstate

/-- Under exact arithmetic, the p. 93 final-correction variant also returns
the exact source sum. -/
theorem fl_kahanFinalCorrectedSum_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanFinalCorrectedSum (FPModel.exactWithUnitRoundoff u0 hu0) n v =
      ∑ i : Fin n, v i := by
  rw [fl_kahanFinalCorrectedSum_eq_add_correction,
    fl_kahanSum_exactWithUnitRoundoff u0 hu0,
    fl_kahanCorrection_exactWithUnitRoundoff u0 hu0]
  simp [FPModel.exactWithUnitRoundoff]

/-! ### Higham Problem 4.10 / Priest six-term example -/

/-- The six-term family from Higham Problem 4.10, due to Priest.  The printed
source is `x₁ = 2^(t+1)`, `x₂ = 2^(t+1)-2`, and
`x₃ = x₄ = x₅ = x₆ = -(2^t-1)`. -/
noncomputable def problem49PriestInput (t : ℕ) : Fin 6 → ℝ :=
  fun i =>
    if i.val = 0 then (2 : ℝ) ^ (t + 1)
    else if i.val = 1 then (2 : ℝ) ^ (t + 1) - 2
    else -((2 : ℝ) ^ t - 1)

/-- Priest's six-term Problem 4.10 family has exact real sum `2`. -/
theorem problem49PriestInput_sum_eq_two (t : ℕ) :
    (∑ i : Fin 6, problem49PriestInput t i) = 2 := by
  norm_num [problem49PriestInput, Fin.sum_univ_succ]
  rw [pow_succ]
  ring_nf
  rfl

/-- The concrete IEEE-single instance in Higham Problem 4.10 uses `t = 24`. -/
theorem problem49PriestInput_t24_sum_eq_two :
    (∑ i : Fin 6, problem49PriestInput 24 i) = 2 := by
  exact problem49PriestInput_sum_eq_two 24

/-- Concrete decimal values of the `t = 24` IEEE-single instance. -/
theorem problem49PriestInput_t24_values :
    problem49PriestInput 24 0 = 33554432 ∧
    problem49PriestInput 24 1 = 33554430 ∧
    problem49PriestInput 24 2 = -16777215 ∧
    problem49PriestInput 24 3 = -16777215 ∧
    problem49PriestInput 24 4 = -16777215 ∧
    problem49PriestInput 24 5 = -16777215 := by
  norm_num [problem49PriestInput]
  rfl

/-- The first value `2^(24+1)` in the concrete Problem 4.10 instance is finite
in IEEE single precision. -/
theorem problem49PriestInput_t24_x1_ieeeSingle_finiteSystem :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      (problem49PriestInput 24 0) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 8388608, (26 : ℤ), ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeSingleFormat]
  · norm_num [FloatingPointFormat.exponentInRange,
      FloatingPointFormat.ieeeSingleFormat]
  · norm_num [problem49PriestInput, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR,
      FloatingPointFormat.ieeeSingleFormat]

/-- The second value `2^(24+1)-2` in the concrete Problem 4.10 instance is
finite in IEEE single precision. -/
theorem problem49PriestInput_t24_x2_ieeeSingle_finiteSystem :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      (problem49PriestInput 24 1) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 16777215, (25 : ℤ), ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeSingleFormat]
  · norm_num [FloatingPointFormat.exponentInRange,
      FloatingPointFormat.ieeeSingleFormat]
  · norm_num [problem49PriestInput, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR,
      FloatingPointFormat.ieeeSingleFormat]
    rfl

/-- The repeated tail value `-(2^24-1)` in the concrete Problem 4.10 instance is
finite in IEEE single precision. -/
theorem problem49PriestInput_t24_tail_ieeeSingle_finiteSystem :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      (problem49PriestInput 24 2) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨true, 16777215, (24 : ℤ), ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeSingleFormat]
  · norm_num [FloatingPointFormat.exponentInRange,
      FloatingPointFormat.ieeeSingleFormat]
  · norm_num [problem49PriestInput, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR,
      FloatingPointFormat.ieeeSingleFormat]

/-- Every displayed input in the concrete Problem 4.10 instance is finite in
IEEE single precision. -/
theorem problem49PriestInput_t24_ieeeSingle_finiteSystem
    (i : Fin 6) :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      (problem49PriestInput 24 i) := by
  fin_cases i
  · simpa [problem49PriestInput] using
      problem49PriestInput_t24_x1_ieeeSingle_finiteSystem
  · simpa [problem49PriestInput] using
      problem49PriestInput_t24_x2_ieeeSingle_finiteSystem
  · simpa [problem49PriestInput] using
      problem49PriestInput_t24_tail_ieeeSingle_finiteSystem
  · simpa [problem49PriestInput] using
      problem49PriestInput_t24_tail_ieeeSingle_finiteSystem
  · simpa [problem49PriestInput] using
      problem49PriestInput_t24_tail_ieeeSingle_finiteSystem
  · simpa [problem49PriestInput] using
      problem49PriestInput_t24_tail_ieeeSingle_finiteSystem

/-- First nontrivial rounding fact in the local IEEE-single finite
round-to-even trace for Problem 4.10: the exact sum of the first two displayed
inputs is the midpoint `67108862`, so the tie-to-even rule selects
`67108864`. -/
theorem problem49PriestInput_t24_first_sum_ieeeSingle_rounds_to_67108864 :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
      (problem49PriestInput 24 0) (problem49PriestInput 24 1) =
        (67108864 : ℝ) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let a : ℝ := fmt.normalizedValue false fmt.maxNormalMantissa (26 : ℤ)
  let b : ℝ := fmt.normalizedValue false fmt.minNormalMantissa (27 : ℤ)
  let x : ℝ := (67108862 : ℝ)
  have hm : fmt.normalizedMantissa fmt.maxNormalMantissa :=
    fmt.maxNormalMantissa_normalized
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    exact ⟨false, (26 : ℤ), Or.inl ⟨rfl, rfl⟩⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have ha_value : a = (67108860 : ℝ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa,
      zpow_neg]
  have hb_value : b = (67108864 : ℝ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.minNormalMantissa,
      zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by norm_num [x]
    rw [abs_of_nonneg hxnonneg]
    constructor
    · norm_num [x, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
    · norm_num [x, fmt, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
        zpow_neg]
      exact Nat.cast_le.mpr (by norm_num)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hxrange
  have hleft :
      a = fmt.normalizedValue false fmt.maxNormalMantissa (26 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x]
  have hodd : ¬ FloatingPointFormat.evenMantissa fmt.maxNormalMantissa := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.maxNormalMantissa, FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hm hleft htie hodd
  change fmt.finiteRoundToEven
      (BasicOp.exact BasicOp.add
        (problem49PriestInput 24 0) (problem49PriestInput 24 1)) =
        (67108864 : ℝ)
  have hxop :
      BasicOp.exact BasicOp.add
        (problem49PriestInput 24 0) (problem49PriestInput 24 1) = x := by
    norm_num [BasicOp.exact, problem49PriestInput, x]
    change ((33554432 : ℕ) : ℝ) + ((33554430 : ℕ) : ℝ) =
      ((67108862 : ℕ) : ℝ)
    rw [← Nat.cast_add]
  rw [hxop]
  simpa [fmt, hb_value] using hround

/-! Source-correct Problem 4.10 aliases.

The original declaration names used `problem49` before the current Chapter 4
PDF/source split was refreshed.  These aliases preserve the existing API while
giving ledger and lookup users names that match the printed problem number. -/

/-- Source-correct alias for the Priest six-term family in Problem 4.10. -/
noncomputable def problem410PriestInput (t : ℕ) : Fin 6 → ℝ :=
  problem49PriestInput t

/-- Priest's six-term Problem 4.10 family has exact real sum `2`. -/
theorem problem410PriestInput_sum_eq_two (t : ℕ) :
    (∑ i : Fin 6, problem410PriestInput t i) = 2 := by
  simpa [problem410PriestInput] using problem49PriestInput_sum_eq_two t

/-- The concrete IEEE-single instance in Higham Problem 4.10 uses `t = 24`. -/
theorem problem410PriestInput_t24_sum_eq_two :
    (∑ i : Fin 6, problem410PriestInput 24 i) = 2 := by
  simpa [problem410PriestInput] using problem49PriestInput_t24_sum_eq_two

/-- Concrete decimal values of the `t = 24` Problem 4.10 instance. -/
theorem problem410PriestInput_t24_values :
    problem410PriestInput 24 0 = 33554432 ∧
    problem410PriestInput 24 1 = 33554430 ∧
    problem410PriestInput 24 2 = -16777215 ∧
    problem410PriestInput 24 3 = -16777215 ∧
    problem410PriestInput 24 4 = -16777215 ∧
    problem410PriestInput 24 5 = -16777215 := by
  simpa [problem410PriestInput] using problem49PriestInput_t24_values

/-- The first value in the concrete Problem 4.10 instance is finite in IEEE
single precision. -/
theorem problem410PriestInput_t24_x1_ieeeSingle_finiteSystem :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      (problem410PriestInput 24 0) := by
  simpa [problem410PriestInput] using
    problem49PriestInput_t24_x1_ieeeSingle_finiteSystem

/-- The second value in the concrete Problem 4.10 instance is finite in IEEE
single precision. -/
theorem problem410PriestInput_t24_x2_ieeeSingle_finiteSystem :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      (problem410PriestInput 24 1) := by
  simpa [problem410PriestInput] using
    problem49PriestInput_t24_x2_ieeeSingle_finiteSystem

/-- The repeated tail value in the concrete Problem 4.10 instance is finite in
IEEE single precision. -/
theorem problem410PriestInput_t24_tail_ieeeSingle_finiteSystem :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      (problem410PriestInput 24 2) := by
  simpa [problem410PriestInput] using
    problem49PriestInput_t24_tail_ieeeSingle_finiteSystem

/-- Every displayed input in the concrete Problem 4.10 instance is finite in
IEEE single precision. -/
theorem problem410PriestInput_t24_ieeeSingle_finiteSystem
    (i : Fin 6) :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      (problem410PriestInput 24 i) := by
  simpa [problem410PriestInput] using
    problem49PriestInput_t24_ieeeSingle_finiteSystem i

/-- First nontrivial rounding fact in the local IEEE-single finite
round-to-even trace for Problem 4.10. -/
theorem problem410PriestInput_t24_first_sum_ieeeSingle_rounds_to_67108864 :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.add
      (problem410PriestInput 24 0) (problem410PriestInput 24 1) =
        (67108864 : ℝ) := by
  simpa [problem410PriestInput] using
    problem49PriestInput_t24_first_sum_ieeeSingle_rounds_to_67108864

/-- Generic algebraic bridge from a Kahan-style backward-error representation
to the corresponding absolute forward-error bound.

This is the checked "corresponding forward bound" step used by Higham's
transition from (4.8) to (4.9); the hard part is still proving the displayed
Knuth/Kahan backward-error witnesses for the concrete rounded trace. -/
lemma kahan_backward_error_forward_bound_core
    {n : ℕ} (v : Fin n → ℝ) {computed B : ℝ}
    (hback :
      ∃ μ : Fin n → ℝ,
        (∀ i, |μ i| ≤ B) ∧
        computed = ∑ i : Fin n, v i * (1 + μ i)) :
    |computed - ∑ i : Fin n, v i| ≤
      B * ∑ i : Fin n, |v i| := by
  rcases hback with ⟨μ, hμ, hcomputed⟩
  have hdecomp :
      computed - ∑ i : Fin n, v i = ∑ i : Fin n, v i * μ i := by
    rw [hcomputed, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hdecomp]
  calc
    |∑ i : Fin n, v i * μ i|
        ≤ ∑ i : Fin n, |v i * μ i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |v i| * |μ i| := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [abs_mul]
    _ ≤ ∑ i : Fin n, |v i| * B :=
          Finset.sum_le_sum fun i _hi =>
            mul_le_mul_of_nonneg_left (hμ i) (abs_nonneg _)
    _ = B * ∑ i : Fin n, |v i| := by
          rw [← Finset.sum_mul, mul_comm]

/-- If the ordinary Kahan returned sum satisfies a backward-error
representation with componentwise perturbation bound `B`, then it satisfies
the corresponding absolute forward-error bound. -/
theorem fl_kahanSum_forward_error_bound_of_backward
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) {B : ℝ}
    (hback :
      ∃ μ : Fin n → ℝ,
        (∀ i, |μ i| ≤ B) ∧
        fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i)) :
    |fl_kahanSum fp n v - ∑ i : Fin n, v i| ≤
      B * ∑ i : Fin n, |v i| :=
  kahan_backward_error_forward_bound_core v hback

/-- Corrected ordinary returned-Kahan forward-error bound corresponding to the
source-honest leading-`3*u` backward-error theorem. -/
theorem fl_kahanSum_forward_error_bound_correctedReturnedMajorant
    (fp : FPModel) (n : Nat) (v : Fin n -> Real)
    (hu64 : fp.u <= 1 / 64)
    (hm : (n : Real) * fp.u ^ 2 <= 1 / 16) :
    |fl_kahanSum fp n v - Finset.univ.sum (fun i : Fin n => v i)| <=
      (3 * fp.u + (14 + 13 * (n : Real)) * fp.u ^ 2 +
        (12 + 13 * (n : Real)) * fp.u ^ 3) *
        Finset.univ.sum (fun i : Fin n => |v i|) := by
  exact
    fl_kahanSum_forward_error_bound_of_backward fp n v
      (fl_kahanSum_backward_error_source_bound_correctedReturnedMajorant
        fp n v hu64 hm)

/-- Corrected terminal corresponding to Higham (4.8) after the bare-model
strength discrepancy above: actual returned Kahan admits a componentwise
backward representation with leading constant 3 and an explicit
n-dependent second- and third-order majorant. -/
theorem highamCh4_equation48_modelStrengthCorrection_bareFPModel
    (fp : FPModel) (n : Nat) (v : Fin n -> Real)
    (hu64 : fp.u <= 1 / 64)
    (hm : (n : Real) * fp.u ^ 2 <= 1 / 16) :
    exists mu : Fin n -> Real,
      (forall i,
        |mu i| <=
          3 * fp.u + (14 + 13 * (n : Real)) * fp.u ^ 2 +
            (12 + 13 * (n : Real)) * fp.u ^ 3) /\
      fl_kahanSum fp n v =
        Finset.univ.sum (fun i : Fin n => v i * (1 + mu i)) :=
  fl_kahanSum_backward_error_source_bound_correctedReturnedMajorant
    fp n v hu64 hm

/-- Corrected terminal corresponding to Higham (4.9) after the bare-model
strength discrepancy above: the actual returned Kahan error has the matching
explicit leading-3 absolute forward bound. -/
theorem highamCh4_equation49_modelStrengthCorrection_bareFPModel
    (fp : FPModel) (n : Nat) (v : Fin n -> Real)
    (hu64 : fp.u <= 1 / 64)
    (hm : (n : Real) * fp.u ^ 2 <= 1 / 16) :
    |fl_kahanSum fp n v - Finset.univ.sum (fun i : Fin n => v i)| <=
      (3 * fp.u + (14 + 13 * (n : Real)) * fp.u ^ 2 +
        (12 + 13 * (n : Real)) * fp.u ^ 3) *
        Finset.univ.sum (fun i : Fin n => |v i|) :=
  fl_kahanSum_forward_error_bound_correctedReturnedMajorant
    fp n v hu64 hm

/-- One-signed relative-error consequence of a supplied ordinary Kahan
backward-error representation. -/
theorem fl_kahanSum_relError_le_of_backward_oneSigned
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) {B : ℝ}
    (hback :
      ∃ μ : Fin n → ℝ,
        (∀ i, |μ i| ≤ B) ∧
        fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i))
    (hv : OneSigned v) (hsum : (∑ i : Fin n, v i) ≠ 0) :
    relError (fl_kahanSum fp n v) (∑ i : Fin n, v i) ≤ B := by
  have hden : 0 < |∑ i : Fin n, v i| := abs_pos.mpr hsum
  have hbound := fl_kahanSum_forward_error_bound_of_backward fp n v hback
  have hbound_one :
      |fl_kahanSum fp n v - ∑ i : Fin n, v i| ≤
        B * |∑ i : Fin n, v i| := by
    simpa [sum_abs_eq_abs_sum_of_oneSigned v hv] using hbound
  unfold relError
  rw [div_le_iff₀ hden]
  exact hbound_one

/-- Forward-error bridge for the final-corrected Kahan variant.  The supplied
backward-error representation can use the stronger bound promised by Kahan's
machine-dependent theorem once that theorem is formalized. -/
theorem fl_kahanFinalCorrectedSum_forward_error_bound_of_backward
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) {B : ℝ}
    (hback :
      ∃ μ : Fin n → ℝ,
        (∀ i, |μ i| ≤ B) ∧
        fl_kahanFinalCorrectedSum fp n v =
          ∑ i : Fin n, v i * (1 + μ i)) :
    |fl_kahanFinalCorrectedSum fp n v - ∑ i : Fin n, v i| ≤
      B * ∑ i : Fin n, |v i| :=
  kahan_backward_error_forward_bound_core v hback

/-- One-signed relative-error consequence for the final-corrected Kahan
variant from a supplied backward-error representation. -/
theorem fl_kahanFinalCorrectedSum_relError_le_of_backward_oneSigned
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) {B : ℝ}
    (hback :
      ∃ μ : Fin n → ℝ,
        (∀ i, |μ i| ≤ B) ∧
        fl_kahanFinalCorrectedSum fp n v =
          ∑ i : Fin n, v i * (1 + μ i))
    (hv : OneSigned v) (hsum : (∑ i : Fin n, v i) ≠ 0) :
    relError (fl_kahanFinalCorrectedSum fp n v)
        (∑ i : Fin n, v i) ≤ B := by
  have hden : 0 < |∑ i : Fin n, v i| := abs_pos.mpr hsum
  have hbound :=
    fl_kahanFinalCorrectedSum_forward_error_bound_of_backward fp n v hback
  have hbound_one :
      |fl_kahanFinalCorrectedSum fp n v - ∑ i : Fin n, v i| ≤
        B * |∑ i : Fin n, v i| := by
    simpa [sum_abs_eq_abs_sum_of_oneSigned v hv] using hbound
  unfold relError
  rw [div_le_iff₀ hden]
  exact hbound_one

/-! ## Ordinary Kahan summation under the no-guard model -/

/-- One ordinary Kahan compensated-summation step evaluated in the no-guard
model.  This is the unmodified Algorithm 4.2 trace, not Kahan's later
machine-dependent no-guard correction. -/
noncomputable def kahanNoGuardStepTrace (fp : NoGuardFPModel) (x : ℝ)
    (state : KahanState) : KahanStepTrace :=
  let temp := state.s
  let y := fp.fl_add x state.e
  let s := fp.fl_add temp y
  let e := fp.fl_add (fp.fl_sub temp s) y
  { temp := temp, y := y, s := s, e := e }

/-- Persistent-state update induced by one ordinary no-guard Kahan step. -/
noncomputable def kahanNoGuardStep (fp : NoGuardFPModel) (x : ℝ)
    (state : KahanState) : KahanState :=
  (kahanNoGuardStepTrace fp x state).nextState

/-- The `temp` assignment in ordinary no-guard Kahan summation. -/
theorem kahanNoGuardStepTrace_temp
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    (kahanNoGuardStepTrace fp x state).temp = state.s := by
  rfl

/-- The `y = x_i + e` assignment in ordinary no-guard Kahan summation. -/
theorem kahanNoGuardStepTrace_y
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    (kahanNoGuardStepTrace fp x state).y = fp.fl_add x state.e := by
  rfl

/-- The `s = temp + y` assignment in ordinary no-guard Kahan summation. -/
theorem kahanNoGuardStepTrace_s
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    (kahanNoGuardStepTrace fp x state).s =
      fp.fl_add (kahanNoGuardStepTrace fp x state).temp
        (kahanNoGuardStepTrace fp x state).y := by
  rfl

/-- The `e = (temp - s) + y` assignment in ordinary no-guard Kahan summation. -/
theorem kahanNoGuardStepTrace_e
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    (kahanNoGuardStepTrace fp x state).e =
      fp.fl_add
        (fp.fl_sub (kahanNoGuardStepTrace fp x state).temp
          (kahanNoGuardStepTrace fp x state).s)
        (kahanNoGuardStepTrace fp x state).y := by
  rfl

/-- State after the first `k` ordinary no-guard Kahan steps. -/
noncomputable def kahanNoGuardPrefixState
    (fp : NoGuardFPModel) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : KahanState :=
  Fin.foldl k
    (fun state i =>
      kahanNoGuardStep fp
        (v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) state)
    KahanState.zero

/-- The per-index ordinary no-guard Kahan trace. -/
noncomputable def kahanNoGuardTrace
    (fp : NoGuardFPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) : KahanStepTrace :=
  kahanNoGuardStepTrace fp (v i)
    (kahanNoGuardPrefixState fp v i.val (Nat.le_of_lt i.isLt))

/-- Final ordinary no-guard Kahan state after all inputs. -/
noncomputable def fl_kahanNoGuardState
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) : KahanState :=
  kahanNoGuardPrefixState fp v n (Nat.le_refl n)

/-- Final sum returned by ordinary Kahan summation in the no-guard model. -/
noncomputable def fl_kahanNoGuardSum
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  (fl_kahanNoGuardState fp n v).s

/-- Final correction retained by ordinary Kahan summation in the no-guard model. -/
noncomputable def fl_kahanNoGuardCorrection
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  (fl_kahanNoGuardState fp n v).e

/-- The final ordinary no-guard state is the explicit prefix state. -/
theorem fl_kahanNoGuardState_eq_prefixState
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanNoGuardState fp n v =
      kahanNoGuardPrefixState fp v n (Nat.le_refl n) := by
  rfl

/-- The ordinary no-guard returned sum is the `s` field of the final state. -/
theorem fl_kahanNoGuardSum_eq_state_s
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanNoGuardSum fp n v =
      (fl_kahanNoGuardState fp n v).s := by
  rfl

/-- The ordinary no-guard retained correction is the `e` field of the final state. -/
theorem fl_kahanNoGuardCorrection_eq_state_e
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanNoGuardCorrection fp n v =
      (fl_kahanNoGuardState fp n v).e := by
  rfl

/-- A concrete no-guard model for a two-term compensated-summation failure.
All operations are exact except the two additions used in the second Kahan
step's ordinary correction formula. -/
noncomputable def kahanNoGuardCounterexampleModel : NoGuardFPModel where
  u := 1 / 4
  unit_roundoff_pos := by norm_num
  fl_add := fun x y =>
    if x = 1 ∧ y = -7 / 8 then 1 / 4
    else if x = 3 / 4 ∧ y = -7 / 8 then 0
    else x + y
  fl_sub := fun x y => x - y
  fl_mul := fun x y => x * y
  fl_div := fun x y => x / y
  model_add := by
    intro x y
    by_cases hbad₁ : x = 1 ∧ y = -7 / 8
    · refine ⟨0, -1 / 7, ?_, ?_, ?_⟩
      · norm_num
      · norm_num
      · rcases hbad₁ with ⟨rfl, rfl⟩
        norm_num [noGuardAddWitness]
    · by_cases hbad₂ : x = 3 / 4 ∧ y = -7 / 8
      · refine ⟨0, -1 / 7, ?_, ?_, ?_⟩
        · norm_num
        · norm_num
        · rcases hbad₂ with ⟨rfl, rfl⟩
          norm_num [hbad₁, noGuardAddWitness]
          rfl
      · refine ⟨0, 0, ?_, ?_, ?_⟩
        · norm_num
        · norm_num
        · simp [hbad₁, hbad₂]
  model_sub := by
    intro x y
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · simp
  model_mul := by
    intro x y
    refine ⟨0, ?_, ?_⟩
    · norm_num
    · unfold signedRelErrorWitness
      ring
  model_div := by
    intro x y _hy
    refine ⟨0, ?_, ?_⟩
    · norm_num
    · unfold signedRelErrorWitness
      ring

/-- The two-term input used by the ordinary no-guard Kahan counterexample. -/
noncomputable def kahanNoGuardCounterexampleInput : Fin 2 → ℝ :=
  fun i => if i.val = 0 then 1 else -7 / 8

/-- The ordinary no-guard Kahan counterexample finishes with `s = 1/4` and
zero correction, although the exact sum is `1/8`. -/
theorem fl_kahanNoGuardCounterexampleState_eq :
    fl_kahanNoGuardState kahanNoGuardCounterexampleModel 2
        kahanNoGuardCounterexampleInput =
      { s := 1 / 4, e := 0 } := by
  norm_num [fl_kahanNoGuardState, kahanNoGuardPrefixState,
    kahanNoGuardStep, kahanNoGuardStepTrace, KahanStepTrace.nextState,
    KahanState.zero, kahanNoGuardCounterexampleModel,
    kahanNoGuardCounterexampleInput, Fin.foldl_succ]

/-- The ordinary no-guard Kahan counterexample returns `1/4`. -/
theorem fl_kahanNoGuardCounterexampleSum_eq :
    fl_kahanNoGuardSum kahanNoGuardCounterexampleModel 2
        kahanNoGuardCounterexampleInput = 1 / 4 := by
  have hstate := fl_kahanNoGuardCounterexampleState_eq
  simpa [fl_kahanNoGuardSum] using congrArg KahanState.s hstate

/-- The ordinary no-guard Kahan counterexample retains zero correction. -/
theorem fl_kahanNoGuardCounterexampleCorrection_eq :
    fl_kahanNoGuardCorrection kahanNoGuardCounterexampleModel 2
        kahanNoGuardCounterexampleInput = 0 := by
  have hstate := fl_kahanNoGuardCounterexampleState_eq
  simpa [fl_kahanNoGuardCorrection] using congrArg KahanState.e hstate

/-- The exact sum of the no-guard Kahan counterexample input is `1/8`. -/
theorem kahanNoGuardCounterexample_exactSum_eq :
    (∑ i : Fin 2, kahanNoGuardCounterexampleInput i) = 1 / 8 := by
  norm_num [kahanNoGuardCounterexampleInput, Fin.sum_univ_two]

/-- Ordinary Kahan compensated summation can have relative error exactly one
under the no-guard model.  This records the algorithm-level failure mode behind
Higham's pp. 94--95 warning that the no-guard model does not guarantee the
standard compensated-summation bound. -/
theorem kahanNoGuardCounterexample_relError_eq_one :
    relError
        (fl_kahanNoGuardSum kahanNoGuardCounterexampleModel 2
          kahanNoGuardCounterexampleInput)
        (∑ i : Fin 2, kahanNoGuardCounterexampleInput i) = 1 := by
  rw [fl_kahanNoGuardCounterexampleSum_eq,
    kahanNoGuardCounterexample_exactSum_eq]
  simpa using noGuardBinaryT3_truncated_relError_eq_one

/-! ## Alternative compensated summation with separately accumulated corrections -/

/-- One step of the p. 94 alternative compensated-summation variant.  The main
sum is updated without immediately feeding the correction back into the next
input; the local correction is stored separately. -/
structure AlternativeCompensatedStepTrace where
  temp : ℝ
  s : ℝ
  e : ℝ

namespace AlternativeCompensatedStepTrace

/-- The main running sum after an alternative compensated-summation step. -/
def nextSum (t : AlternativeCompensatedStepTrace) : ℝ :=
  t.s

end AlternativeCompensatedStepTrace

/-- One rounded step of the alternative compensated-summation variant:
`temp = s; s = temp + x_i; e_i = (temp - s) + x_i`. -/
noncomputable def alternativeCompensatedStepTrace
    (fp : FPModel) (x : ℝ) (sum : ℝ) : AlternativeCompensatedStepTrace :=
  let temp := sum
  let s := fp.fl_add temp x
  let e := fp.fl_add (fp.fl_sub temp s) x
  { temp := temp, s := s, e := e }

/-- The `temp` assignment in the alternative compensated-summation variant. -/
theorem alternativeCompensatedStepTrace_temp
    (fp : FPModel) (x sum : ℝ) :
    (alternativeCompensatedStepTrace fp x sum).temp = sum := by
  rfl

/-- The main `s = temp + x_i` assignment in the alternative variant. -/
theorem alternativeCompensatedStepTrace_s
    (fp : FPModel) (x sum : ℝ) :
    (alternativeCompensatedStepTrace fp x sum).s =
      fp.fl_add (alternativeCompensatedStepTrace fp x sum).temp x := by
  rfl

/-- The stored correction `e_i = (temp - s) + x_i`, in the displayed Kahan
correction evaluation order but without immediate feedback into the main sum. -/
theorem alternativeCompensatedStepTrace_e
    (fp : FPModel) (x sum : ℝ) :
    (alternativeCompensatedStepTrace fp x sum).e =
      fp.fl_add
        (fp.fl_sub (alternativeCompensatedStepTrace fp x sum).temp
          (alternativeCompensatedStepTrace fp x sum).s)
        x := by
  rfl

/-- The local correction pair in one step of the p. 94 alternative variant is
exactly the Chapter 4 equation-(4.7) correction-formula trace applied to
`temp` and the current input. -/
theorem alternativeCompensatedStepTrace_correctionFormulaTrace
    (fp : FPModel) (x sum : ℝ) :
    ({ s := (alternativeCompensatedStepTrace fp x sum).s,
       e := (alternativeCompensatedStepTrace fp x sum).e } :
        CorrectionFormulaTrace) =
      correctionFormulaTrace fp
        (alternativeCompensatedStepTrace fp x sum).temp x := by
  simp [alternativeCompensatedStepTrace, correctionFormulaTrace]

/-- If the local correction formula is exact for one step of the p. 94
alternative variant, then that step's main sum plus stored correction equals
the previous main sum plus the current input. -/
theorem alternativeCompensatedStepTrace_main_plus_correction_eq_of_correction
    (fp : FPModel) (x sum : ℝ)
    (hcorr :
      CorrectionFormulaTrace.exact sum x
        ({ s := (alternativeCompensatedStepTrace fp x sum).s,
           e := (alternativeCompensatedStepTrace fp x sum).e } :
          CorrectionFormulaTrace)) :
    (alternativeCompensatedStepTrace fp x sum).s +
        (alternativeCompensatedStepTrace fp x sum).e =
      sum + x := by
  exact hcorr.symm

/-- Main running sum after the first `k` alternative compensated-summation
steps over a length-`n` input.  Corrections are not fed back into this prefix
state. -/
noncomputable def alternativeCompensatedPrefixSum (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : ℝ :=
  Fin.foldl k
    (fun sum i =>
      (alternativeCompensatedStepTrace fp
        (v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) sum).nextSum)
    0

/-- The per-index alternative compensated-summation trace, using the main
prefix sum before index `i`. -/
noncomputable def alternativeCompensatedTrace (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) : AlternativeCompensatedStepTrace :=
  alternativeCompensatedStepTrace fp (v i)
    (alternativeCompensatedPrefixSum fp v i.val (Nat.le_of_lt i.isLt))

/-- The correction sequence `e_i` that is accumulated separately. -/
noncomputable def alternativeCompensatedCorrections (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (alternativeCompensatedTrace fp v i).e

/-- The main prefix in the p. 94 alternative compensated-summation variant is
ordinary left-to-right recursive summation on the processed prefix. -/
theorem alternativeCompensatedPrefixSum_eq_fl_recursiveSum_prefix
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) :
    alternativeCompensatedPrefixSum fp v k hk =
      fl_recursiveSum fp k
        (fun i : Fin k => v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) := by
  simp [alternativeCompensatedPrefixSum, fl_recursiveSum,
    alternativeCompensatedStepTrace, AlternativeCompensatedStepTrace.nextSum]

/-- The local pre-rounding main-add input in the p. 94 alternative variant is
the same `fl_partialSums` quantity used in Higham §4.2's running-error bound
for ordinary recursive summation. -/
theorem alternativeCompensatedTrace_main_add_input_eq_fl_partialSums
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    (alternativeCompensatedTrace fp v i).temp + v i =
      fl_partialSums fp v i := by
  simp [alternativeCompensatedTrace, alternativeCompensatedStepTrace,
    fl_partialSums, alternativeCompensatedPrefixSum_eq_fl_recursiveSum_prefix]

/-- The stored correction generated at index `i` during a `k`-step prefix of
the alternative compensated-summation trace. -/
noncomputable def alternativeCompensatedPrefixCorrection
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (i : Fin k) : ℝ :=
  (alternativeCompensatedStepTrace fp
      (v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩)
      (alternativeCompensatedPrefixSum fp v i.val
        (Nat.le_trans (Nat.le_of_lt i.isLt) hk))).e

/-- Prefix invariant for the p. 94 alternative compensated-summation trace.

If every local correction formula is exact, then the main prefix sum plus the
exact sum of the stored local corrections equals the exact source prefix sum. -/
theorem alternativeCompensatedPrefixSum_add_corrections_eq_sum_of_exact_steps
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      (∀ i : Fin k,
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        let sum :=
          alternativeCompensatedPrefixSum fp v i.val
            (Nat.le_trans (Nat.le_of_lt i.isLt) hk)
        let trace := alternativeCompensatedStepTrace fp (v idx) sum
        CorrectionFormulaTrace.exact sum (v idx)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace)) →
      alternativeCompensatedPrefixSum fp v k hk +
          ∑ i : Fin k, alternativeCompensatedPrefixCorrection fp v k hk i =
        ∑ i : Fin k, v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  | 0, _hk, _hexact => by
      simp [alternativeCompensatedPrefixSum,
        alternativeCompensatedPrefixCorrection]
  | k + 1, hk, hexact => by
      have hprev_le : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let prev := alternativeCompensatedPrefixSum fp v k hprev_le
      let idx : Fin n :=
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let trace := alternativeCompensatedStepTrace fp (v idx) prev
      have hfold :
          alternativeCompensatedPrefixSum fp v (k + 1) hk =
            trace.s := by
        unfold alternativeCompensatedPrefixSum
        rw [Fin.foldl_succ_last]
        rfl
      have hprev :
          prev +
              ∑ i : Fin k,
                alternativeCompensatedPrefixCorrection fp v k hprev_le i =
            ∑ i : Fin k,
              v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hprev_le⟩ := by
        apply
          alternativeCompensatedPrefixSum_add_corrections_eq_sum_of_exact_steps
            fp v
        intro i
        simpa [alternativeCompensatedPrefixCorrection, prev, idx, trace]
          using hexact i.castSucc
      have hlocal := hexact (Fin.last k)
      have hstep :
          trace.s + trace.e = prev + v idx := by
        exact
          alternativeCompensatedStepTrace_main_plus_correction_eq_of_correction
            fp (v idx) prev hlocal
      rw [hfold]
      rw [Fin.sum_univ_castSucc]
      rw [Fin.sum_univ_castSucc]
      calc
        trace.s +
            (∑ x : Fin k,
                alternativeCompensatedPrefixCorrection fp v (k + 1) hk
                  x.castSucc +
              alternativeCompensatedPrefixCorrection fp v (k + 1) hk
                (Fin.last k)) =
          (trace.s + trace.e) +
              ∑ i : Fin k,
                alternativeCompensatedPrefixCorrection fp v k hprev_le i := by
            simp [alternativeCompensatedPrefixCorrection, trace, prev, idx]
            ring
        _ = (prev + v idx) +
              ∑ i : Fin k,
                alternativeCompensatedPrefixCorrection fp v k hprev_le i := by
            rw [hstep]
        _ = (prev +
              ∑ i : Fin k,
                alternativeCompensatedPrefixCorrection fp v k hprev_le i) +
              v idx := by
            ring
        _ = (∑ i : Fin k,
              v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hprev_le⟩) + v idx := by
            rw [hprev]

/-- The main computed sum before applying the global correction. -/
noncomputable def fl_alternativeCompensatedMainSum
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  alternativeCompensatedPrefixSum fp v n (Nat.le_refl n)

/-- The global correction obtained by recursive summation of the stored local
corrections. -/
noncomputable def fl_alternativeCompensatedGlobalCorrection
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  fl_recursiveSum fp n (alternativeCompensatedCorrections fp v)

/-- Final value of the p. 94 alternative compensated-summation variant: add
the recursively accumulated global correction to the computed main sum. -/
noncomputable def fl_alternativeCompensatedSum
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  fp.fl_add (fl_alternativeCompensatedMainSum fp n v)
    (fl_alternativeCompensatedGlobalCorrection fp n v)

/-- The main sum is the explicit `n`-step alternative prefix sum. -/
theorem fl_alternativeCompensatedMainSum_eq_prefixSum
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) :
    fl_alternativeCompensatedMainSum fp n v =
      alternativeCompensatedPrefixSum fp v n (Nat.le_refl n) := by
  rfl

/-- The global correction is recursive summation of the stored local
corrections. -/
theorem fl_alternativeCompensatedGlobalCorrection_eq_recursiveSum
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) :
    fl_alternativeCompensatedGlobalCorrection fp n v =
      fl_recursiveSum fp n (alternativeCompensatedCorrections fp v) := by
  rfl

/-- The final alternative compensated sum is the rounded add of the main
computed sum and global correction. -/
theorem fl_alternativeCompensatedSum_eq_add_globalCorrection
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) :
    fl_alternativeCompensatedSum fp n v =
      fp.fl_add (fl_alternativeCompensatedMainSum fp n v)
        (fl_alternativeCompensatedGlobalCorrection fp n v) := by
  rfl

/-- Full-length form of the exact-step invariant for the p. 94 alternative
compensated-summation trace.  If each local correction formula is exact, then
the final main sum plus the exact sum of stored corrections is the exact
source sum. -/
theorem fl_alternativeCompensatedMainSum_add_exact_corrections_eq_sum_of_exact_steps
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace)) :
    fl_alternativeCompensatedMainSum fp n v +
        ∑ i : Fin n, alternativeCompensatedCorrections fp v i =
      ∑ i : Fin n, v i := by
  simpa [fl_alternativeCompensatedMainSum,
    alternativeCompensatedCorrections, alternativeCompensatedTrace,
    alternativeCompensatedPrefixCorrection] using
    alternativeCompensatedPrefixSum_add_corrections_eq_sum_of_exact_steps
      fp v n (Nat.le_refl n) hexact

/-- Prefix correction sums in the p. 94 alternative compensated-summation
variant are controlled by the ordinary recursive-summation forward-error bound.

For a `k`-step prefix, exact local correction formulas imply
`main_prefix + exact_corrections = exact_prefix`.  Since the main prefix is
ordinary recursive summation on the same prefix, the exact sum of stored
corrections is exactly the negative main recursive-summation error. -/
theorem alternativeCompensatedPrefixCorrections_abs_le_recursiveSum_forward
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n)
    (hexact :
      ∀ i : Fin k,
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        let sum :=
          alternativeCompensatedPrefixSum fp v i.val
            (Nat.le_trans (Nat.le_of_lt i.isLt) hk)
        let trace := alternativeCompensatedStepTrace fp (v idx) sum
        CorrectionFormulaTrace.exact sum (v idx)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (k - 1)) :
    |∑ i : Fin k, alternativeCompensatedPrefixCorrection fp v k hk i| ≤
      gamma fp (k - 1) *
        ∑ i : Fin k, |v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩| := by
  let pref : Fin k → ℝ :=
    fun i => v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  let main := alternativeCompensatedPrefixSum fp v k hk
  let corr :=
    ∑ i : Fin k, alternativeCompensatedPrefixCorrection fp v k hk i
  have hmain_eq :
      main = fl_recursiveSum fp k pref := by
    simpa [main, pref] using
      alternativeCompensatedPrefixSum_eq_fl_recursiveSum_prefix fp v k hk
  have hcorr_eq :
      main + corr = ∑ i : Fin k, pref i := by
    simpa [main, corr, pref] using
      alternativeCompensatedPrefixSum_add_corrections_eq_sum_of_exact_steps
        fp v k hk hexact
  have hcorr_abs :
      |corr| = |main - ∑ i : Fin k, pref i| := by
    have hcorr_sub : corr = ∑ i : Fin k, pref i - main := by
      linarith
    rw [hcorr_sub, abs_sub_comm]
  calc
    |∑ i : Fin k, alternativeCompensatedPrefixCorrection fp v k hk i|
        = |corr| := by rfl
    _ = |main - ∑ i : Fin k, pref i| := hcorr_abs
    _ = |fl_recursiveSum fp k pref - ∑ i : Fin k, pref i| := by
      rw [hmain_eq]
    _ ≤ gamma fp (k - 1) * ∑ i : Fin k, |pref i| :=
      recursiveSum_forward_error_bound fp k pref hgamma
    _ = gamma fp (k - 1) *
        ∑ i : Fin k, |v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩| := by
      rfl

/-- Full-input specialization of
`alternativeCompensatedPrefixCorrections_abs_le_recursiveSum_forward` for the
prefix ending at index `i`. -/
theorem alternativeCompensatedPrefixCorrections_abs_le_recursiveSum_forward_of_full_exact
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (i : Fin n) (hgamma : gammaValid fp i.val) :
    |∑ j : Fin (i.val + 1),
        alternativeCompensatedPrefixCorrection fp v (i.val + 1)
          (Nat.succ_le_of_lt i.isLt) j| ≤
      gamma fp i.val *
        ∑ j : Fin (i.val + 1),
          |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
            (Nat.succ_le_of_lt i.isLt)⟩| := by
  have hprefixExact :
      ∀ j : Fin (i.val + 1),
        let idx : Fin n :=
          ⟨j.val, Nat.lt_of_lt_of_le j.isLt
            (Nat.succ_le_of_lt i.isLt)⟩
        let sum :=
          alternativeCompensatedPrefixSum fp v j.val
            (Nat.le_trans (Nat.le_of_lt j.isLt)
              (Nat.succ_le_of_lt i.isLt))
        let trace := alternativeCompensatedStepTrace fp (v idx) sum
        CorrectionFormulaTrace.exact sum (v idx)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace) := by
    intro j
    let idx : Fin n :=
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt
        (Nat.succ_le_of_lt i.isLt)⟩
    simpa [idx] using hexact idx
  simpa [Nat.add_sub_cancel] using
    alternativeCompensatedPrefixCorrections_abs_le_recursiveSum_forward
      fp v (i.val + 1) (Nat.succ_le_of_lt i.isLt) hprefixExact hgamma

/-- A computed correction partial sum is bounded by the corresponding exact
correction prefix plus the running error from recursively summing the earlier
stored corrections.

This is the pointwise algebraic split needed for the aggregate equation-(4.10)
running-error budget: the exact-prefix term is controlled by
`alternativeCompensatedPrefixCorrections_abs_le_recursiveSum_forward_of_full_exact`,
while the second term is the recursive-summation error of the correction list
itself. -/
theorem fl_partialSums_alternativeCompensatedCorrections_abs_le_exact_prefix_add_running_error
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
      |∑ j : Fin (i.val + 1),
          alternativeCompensatedPrefixCorrection fp v (i.val + 1)
            (Nat.succ_le_of_lt i.isLt) j| +
        fp.u *
          ∑ j : Fin i.val,
            |fl_partialSums fp
              (fun t : Fin i.val =>
                alternativeCompensatedCorrections fp v
                  ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j| := by
  let corr : Fin n → ℝ := alternativeCompensatedCorrections fp v
  let prevCorr : Fin i.val → ℝ :=
    fun t => corr ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩
  let prevComp := fl_recursiveSum fp i.val prevCorr
  let prevExact := ∑ t : Fin i.val, prevCorr t
  let exactPrefix :=
    ∑ j : Fin (i.val + 1),
      alternativeCompensatedPrefixCorrection fp v (i.val + 1)
        (Nat.succ_le_of_lt i.isLt) j
  have hpartial :
      fl_partialSums fp corr i = prevComp + corr i := by
    simp [fl_partialSums, corr, prevCorr, prevComp]
  have hprefix :
      exactPrefix = prevExact + corr i := by
    dsimp [exactPrefix, prevExact, prevCorr, corr]
    rw [Fin.sum_univ_castSucc]
    simp [alternativeCompensatedPrefixCorrection,
      alternativeCompensatedCorrections, alternativeCompensatedTrace]
  have hdecomp :
      fl_partialSums fp corr i =
        exactPrefix + (prevComp - prevExact) := by
    rw [hpartial, hprefix]
    ring
  have hrun :
      |prevComp - prevExact| ≤
        fp.u * ∑ j : Fin i.val, |fl_partialSums fp prevCorr j| := by
    simpa [prevComp, prevExact, prevCorr] using
      recursiveSum_running_error_bound fp i.val prevCorr
  calc
    |fl_partialSums fp corr i|
        = |exactPrefix + (prevComp - prevExact)| := by rw [hdecomp]
    _ ≤ |exactPrefix| + |prevComp - prevExact| := abs_add_le _ _
    _ ≤ |exactPrefix| +
        fp.u * ∑ j : Fin i.val, |fl_partialSums fp prevCorr j| := by
          exact add_le_add_right hrun _
    _ =
        |∑ j : Fin (i.val + 1),
          alternativeCompensatedPrefixCorrection fp v (i.val + 1)
            (Nat.succ_le_of_lt i.isLt) j| +
        fp.u *
          ∑ j : Fin i.val,
            |fl_partialSums fp
              (fun t : Fin i.val =>
                alternativeCompensatedCorrections fp v
                  ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j| := by
      rfl

/-- Reindex a prefix over `Fin k` as the corresponding filtered sum over
`Fin n`.  Local copy for the compensated-summation prefix bookkeeping. -/
private lemma compensated_sum_fin_eq_sum_filter_lt {n k : ℕ} (hk : k ≤ n)
    (f : Fin n → ℝ) :
    (∑ t : Fin k, f ⟨t.val, by omega⟩) =
      Finset.sum (Finset.filter (fun j : Fin n => j.val < k) Finset.univ) f := by
  classical
  have hinj : ∀ a : Fin k, a ∈ Finset.univ →
      ∀ b : Fin k, b ∈ Finset.univ →
      (⟨a.val, by omega⟩ : Fin n) = ⟨b.val, by omega⟩ → a = b :=
    fun a _ b _ hab => Fin.ext (by simp only [Fin.mk.injEq] at hab; exact hab)
  have himg : Finset.image (fun (t : Fin k) => (⟨t.val, by omega⟩ : Fin n))
      Finset.univ = Finset.filter (fun j : Fin n => j.val < k) Finset.univ := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨t, rfl⟩
      simp
    · intro hj
      exact ⟨⟨j.val, hj⟩, Fin.ext (by simp)⟩
  rw [← himg, Finset.sum_image hinj]

/-- Recursive-summation pre-rounding partial sums are compatible with taking a
prefix of the input list. -/
private lemma fl_partialSums_prefix_restrict_eq
    (fp : FPModel) {n : ℕ} (w : Fin n → ℝ) (i : Fin n) (j : Fin i.val) :
    fl_partialSums fp
        (fun t : Fin i.val =>
          w ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j =
      fl_partialSums fp w
        ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ := by
  simp [fl_partialSums]

/-- A prefix sum of absolute values of computed pre-rounding partial sums is
bounded by the full absolute sum. -/
private lemma fl_partialSums_prefix_abs_sum_le_total
    (fp : FPModel) {n : ℕ} (w : Fin n → ℝ) (i : Fin n) :
    ∑ j : Fin i.val,
        |fl_partialSums fp
          (fun t : Fin i.val =>
            w ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j| ≤
      ∑ j : Fin n, |fl_partialSums fp w j| := by
  classical
  have hprefix_eq :
      (∑ j : Fin i.val,
          |fl_partialSums fp
            (fun t : Fin i.val =>
              w ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j|) =
        Finset.sum
          (Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ)
          (fun j => |fl_partialSums fp w j|) := by
    calc
      (∑ j : Fin i.val,
          |fl_partialSums fp
            (fun t : Fin i.val =>
              w ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j|)
          =
            ∑ j : Fin i.val,
              |fl_partialSums fp w
                ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩| := by
              apply Finset.sum_congr rfl
              intro j _hj
              rw [fl_partialSums_prefix_restrict_eq]
      _ =
        Finset.sum
          (Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ)
          (fun j => |fl_partialSums fp w j|) := by
        simpa using
          (compensated_sum_fin_eq_sum_filter_lt (n := n) (k := i.val)
            (Nat.le_of_lt i.isLt) (fun j : Fin n => |fl_partialSums fp w j|))
  rw [hprefix_eq]
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun j : Fin n => j.val < i.val) Finset.univ)
      (by
        intro j _hj _hnot
        exact abs_nonneg (fl_partialSums fp w j))

/-- Aggregate form of
`fl_partialSums_alternativeCompensatedCorrections_abs_le_exact_prefix_add_running_error`.

The sum of computed correction-list partials is bounded by the sum of exact
correction prefixes plus a self term coming from the recursive summation of
previous stored corrections. -/
theorem alternativeCompensatedCorrections_partialSums_abs_sum_le_exact_prefixes_plus_self
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∑ i : Fin n,
        |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
      ∑ i : Fin n,
          |∑ j : Fin (i.val + 1),
            alternativeCompensatedPrefixCorrection fp v (i.val + 1)
              (Nat.succ_le_of_lt i.isLt) j| +
        (n : ℝ) * fp.u *
          ∑ i : Fin n,
            |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| := by
  let corr : Fin n → ℝ := alternativeCompensatedCorrections fp v
  let total : ℝ := ∑ i : Fin n, |fl_partialSums fp corr i|
  let exactBudget : ℝ :=
    ∑ i : Fin n,
      |∑ j : Fin (i.val + 1),
        alternativeCompensatedPrefixCorrection fp v (i.val + 1)
          (Nat.succ_le_of_lt i.isLt) j|
  have hpoint :
      ∀ i : Fin n,
        |fl_partialSums fp corr i| ≤
          |∑ j : Fin (i.val + 1),
            alternativeCompensatedPrefixCorrection fp v (i.val + 1)
              (Nat.succ_le_of_lt i.isLt) j| +
            fp.u * total := by
    intro i
    have hsplit :=
      fl_partialSums_alternativeCompensatedCorrections_abs_le_exact_prefix_add_running_error
        fp v i
    have hprefix :
        ∑ j : Fin i.val,
            |fl_partialSums fp
              (fun t : Fin i.val => corr
                ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j| ≤
          total := by
      simpa [total, corr] using
        fl_partialSums_prefix_abs_sum_le_total fp corr i
    have hrun :
        fp.u *
            ∑ j : Fin i.val,
              |fl_partialSums fp
                (fun t : Fin i.val => corr
                  ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j| ≤
              fp.u * total :=
      mul_le_mul_of_nonneg_left hprefix fp.u_nonneg
    exact le_trans (by simpa [corr] using hsplit) (by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hrun
          (|∑ j : Fin (i.val + 1),
            alternativeCompensatedPrefixCorrection fp v (i.val + 1)
              (Nat.succ_le_of_lt i.isLt) j|))
  calc
    ∑ i : Fin n, |fl_partialSums fp corr i|
        ≤ ∑ i : Fin n,
            (|∑ j : Fin (i.val + 1),
              alternativeCompensatedPrefixCorrection fp v (i.val + 1)
                (Nat.succ_le_of_lt i.isLt) j| + fp.u * total) := by
          exact Finset.sum_le_sum (fun i _hi => hpoint i)
    _ =
        exactBudget + (n : ℝ) * fp.u * total := by
          simp [exactBudget, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
    _ =
      ∑ i : Fin n,
          |∑ j : Fin (i.val + 1),
            alternativeCompensatedPrefixCorrection fp v (i.val + 1)
              (Nat.succ_le_of_lt i.isLt) j| +
        (n : ℝ) * fp.u *
          ∑ i : Fin n,
            |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| := by
      rfl

/-- Absorb the self term in
`alternativeCompensatedCorrections_partialSums_abs_sum_le_exact_prefixes_plus_self`.

Under the source smallness condition `n*u <= 1/10`, it suffices to bound the
exact correction-prefix aggregate by `0.9 * n^2*u*sum_i |x_i|` in order to
obtain the running-error budget required by the equation-(4.10) bridge. -/
theorem alternativeCompensatedCorrectionRunningErrorBudget_of_exact_prefix_budget
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 10)
    (hprefixBudget :
      ∑ i : Fin n,
          |∑ j : Fin (i.val + 1),
            alternativeCompensatedPrefixCorrection fp v (i.val + 1)
              (Nat.succ_le_of_lt i.isLt) j| ≤
        (9 / 10 : ℝ) * ((n : ℝ) ^ 2 * fp.u) *
          ∑ i : Fin n, |v i|) :
    fp.u *
        ∑ i : Fin n,
          |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
      ((n : ℝ) ^ 2 * fp.u ^ 2) * ∑ i : Fin n, |v i| := by
  let corr : Fin n → ℝ := alternativeCompensatedCorrections fp v
  let P : ℝ := ∑ i : Fin n, |fl_partialSums fp corr i|
  let E : ℝ :=
    ∑ i : Fin n,
      |∑ j : Fin (i.val + 1),
        alternativeCompensatedPrefixCorrection fp v (i.val + 1)
          (Nat.succ_le_of_lt i.isLt) j|
  let S : ℝ := ∑ i : Fin n, |v i|
  have hP_nonneg : 0 ≤ P := by
    exact Finset.sum_nonneg fun i _hi => abs_nonneg (fl_partialSums fp corr i)
  have hsplit : P ≤ E + ((n : ℝ) * fp.u) * P := by
    simpa [P, E, corr, mul_assoc] using
      alternativeCompensatedCorrections_partialSums_abs_sum_le_exact_prefixes_plus_self
        fp v
  have hself_le : ((n : ℝ) * fp.u) * P ≤ (1 / 10 : ℝ) * P := by
    exact mul_le_mul_of_nonneg_right hsmall hP_nonneg
  have hE_lower : (9 / 10 : ℝ) * P ≤ E := by
    nlinarith
  have hP_le : P ≤ (10 / 9 : ℝ) * E := by
    nlinarith
  have hprefixBudget' :
      E ≤ (9 / 10 : ℝ) * ((n : ℝ) ^ 2 * fp.u) * S := by
    simpa [E, S] using hprefixBudget
  have hscale :
      (10 / 9 : ℝ) * E ≤
        (10 / 9 : ℝ) *
          ((9 / 10 : ℝ) * ((n : ℝ) ^ 2 * fp.u) * S) := by
    exact mul_le_mul_of_nonneg_left hprefixBudget' (by norm_num)
  calc
    fp.u * ∑ i : Fin n,
          |fl_partialSums fp (alternativeCompensatedCorrections fp v) i|
        = fp.u * P := by rfl
    _ ≤ fp.u * ((10 / 9 : ℝ) * E) := by
      exact mul_le_mul_of_nonneg_left hP_le fp.u_nonneg
    _ ≤ fp.u *
          ((10 / 9 : ℝ) *
            ((9 / 10 : ℝ) * ((n : ℝ) ^ 2 * fp.u) * S)) := by
      exact mul_le_mul_of_nonneg_left hscale fp.u_nonneg
    _ = ((n : ℝ) ^ 2 * fp.u ^ 2) * ∑ i : Fin n, |v i| := by
      simp [S]
      ring

/-- Under `k*u <= 0.1`, Higham's `gamma_k` is bounded by
`(10/9) * k*u`. -/
private lemma gamma_le_ten_ninth_mul_of_nu_le_tenth
    (fp : FPModel) (k : ℕ)
    (hsmall : (k : ℝ) * fp.u ≤ 1 / 10) :
    gamma fp k ≤ (10 / 9 : ℝ) * ((k : ℝ) * fp.u) := by
  set a : ℝ := (k : ℝ) * fp.u
  have ha_nonneg : 0 ≤ a := by
    exact mul_nonneg (by exact_mod_cast Nat.zero_le k) fp.u_nonneg
  have hden_pos : 0 < 1 - a := by
    nlinarith
  unfold gamma
  change a / (1 - a) ≤ (10 / 9 : ℝ) * a
  rw [div_le_iff₀ hden_pos]
  nlinarith

/-- Twice the sum of the zero-based `Fin n` indices is at most `n^2`. -/
private lemma two_mul_sum_fin_val_cast_le_sq (n : ℕ) :
    2 * (∑ i : Fin n, (i.val : ℝ)) ≤ (n : ℝ) ^ 2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp
      nlinarith

/-- The absolute source mass in a prefix is bounded by the full absolute source
mass. -/
private lemma alternativeCompensatedPrefix_input_abs_sum_le_total
    {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    ∑ j : Fin (i.val + 1),
        |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
          (Nat.succ_le_of_lt i.isLt)⟩| ≤
      ∑ j : Fin n, |v j| := by
  classical
  have hprefix_eq :
      (∑ j : Fin (i.val + 1),
          |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
            (Nat.succ_le_of_lt i.isLt)⟩|) =
        Finset.sum
          (Finset.filter (fun j : Fin n => j.val < i.val + 1) Finset.univ)
          (fun j => |v j|) := by
    simpa using
      (compensated_sum_fin_eq_sum_filter_lt (n := n) (k := i.val + 1)
        (Nat.succ_le_of_lt i.isLt) (fun j : Fin n => |v j|))
  rw [hprefix_eq]
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun j : Fin n => j.val < i.val + 1) Finset.univ)
      (by
        intro j _hj _hnot
        exact abs_nonneg (v j))

/-- The exact correction-prefix aggregate is controlled by the usual
recursive-summation forward-error bound for each prefix.  Under `n*u <= 0.1`,
the aggregate is at most `(5/9) * n^2*u*sum_i |x_i|`. -/
theorem alternativeCompensatedCorrectionExactPrefixes_abs_sum_le_five_ninth_n_sq_u
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 10) :
    ∑ i : Fin n,
        |∑ j : Fin (i.val + 1),
          alternativeCompensatedPrefixCorrection fp v (i.val + 1)
            (Nat.succ_le_of_lt i.isLt) j| ≤
      (5 / 9 : ℝ) * ((n : ℝ) ^ 2 * fp.u) *
        ∑ i : Fin n, |v i| := by
  let S : ℝ := ∑ i : Fin n, |v i|
  have hS_nonneg : 0 ≤ S := by
    exact Finset.sum_nonneg fun i _hi => abs_nonneg (v i)
  have hpoint :
      ∀ i : Fin n,
        |∑ j : Fin (i.val + 1),
          alternativeCompensatedPrefixCorrection fp v (i.val + 1)
            (Nat.succ_le_of_lt i.isLt) j| ≤
          (10 / 9 : ℝ) * ((i.val : ℝ) * fp.u) * S := by
    intro i
    have hi_le_n : (i.val : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.le_of_lt i.isLt
    have hi_small : (i.val : ℝ) * fp.u ≤ 1 / 10 := by
      exact le_trans (mul_le_mul_of_nonneg_right hi_le_n fp.u_nonneg) hsmall
    have hvalid_i : gammaValid fp i.val := by
      unfold gammaValid
      nlinarith
    have hprefix :=
      alternativeCompensatedPrefixCorrections_abs_le_recursiveSum_forward_of_full_exact
        fp v hexact i hvalid_i
    have hgamma_le :
        gamma fp i.val ≤ (10 / 9 : ℝ) * ((i.val : ℝ) * fp.u) :=
      gamma_le_ten_ninth_mul_of_nu_le_tenth fp i.val hi_small
    have hprefix_abs :
        ∑ j : Fin (i.val + 1),
            |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
              (Nat.succ_le_of_lt i.isLt)⟩| ≤ S := by
      simpa [S] using alternativeCompensatedPrefix_input_abs_sum_le_total v i
    have hprefix_abs_nonneg :
        0 ≤ ∑ j : Fin (i.val + 1),
            |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
              (Nat.succ_le_of_lt i.isLt)⟩| := by
      exact Finset.sum_nonneg fun j _hj => abs_nonneg _
    have hcoef_nonneg :
        0 ≤ (10 / 9 : ℝ) * ((i.val : ℝ) * fp.u) := by
      exact mul_nonneg (by norm_num)
        (mul_nonneg (by exact_mod_cast Nat.zero_le i.val) fp.u_nonneg)
    calc
      |∑ j : Fin (i.val + 1),
        alternativeCompensatedPrefixCorrection fp v (i.val + 1)
          (Nat.succ_le_of_lt i.isLt) j|
          ≤ gamma fp i.val *
              ∑ j : Fin (i.val + 1),
                |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
                  (Nat.succ_le_of_lt i.isLt)⟩| := hprefix
      _ ≤ ((10 / 9 : ℝ) * ((i.val : ℝ) * fp.u)) *
              ∑ j : Fin (i.val + 1),
                |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
                  (Nat.succ_le_of_lt i.isLt)⟩| := by
            exact mul_le_mul_of_nonneg_right hgamma_le hprefix_abs_nonneg
      _ ≤ ((10 / 9 : ℝ) * ((i.val : ℝ) * fp.u)) * S := by
            exact mul_le_mul_of_nonneg_left hprefix_abs hcoef_nonneg
      _ = (10 / 9 : ℝ) * ((i.val : ℝ) * fp.u) * S := by
            ring
  have hsum :
      ∑ i : Fin n,
          |∑ j : Fin (i.val + 1),
            alternativeCompensatedPrefixCorrection fp v (i.val + 1)
              (Nat.succ_le_of_lt i.isLt) j| ≤
        ∑ i : Fin n, (10 / 9 : ℝ) * ((i.val : ℝ) * fp.u) * S := by
    exact Finset.sum_le_sum (fun i _hi => hpoint i)
  have hsum_simplified :
      ∑ i : Fin n, (10 / 9 : ℝ) * ((i.val : ℝ) * fp.u) * S =
        (10 / 9 : ℝ) * fp.u * S *
          ∑ i : Fin n, (i.val : ℝ) := by
    symm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hidx_le : ∑ i : Fin n, (i.val : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
    have htwo := two_mul_sum_fin_val_cast_le_sq n
    nlinarith
  have hcoef_nonneg : 0 ≤ (10 / 9 : ℝ) * fp.u * S := by
    exact mul_nonneg (mul_nonneg (by norm_num) fp.u_nonneg) hS_nonneg
  have hweighted :
      (10 / 9 : ℝ) * fp.u * S *
          ∑ i : Fin n, (i.val : ℝ) ≤
        (10 / 9 : ℝ) * fp.u * S * ((n : ℝ) ^ 2 / 2) := by
    exact mul_le_mul_of_nonneg_left hidx_le hcoef_nonneg
  calc
    ∑ i : Fin n,
        |∑ j : Fin (i.val + 1),
          alternativeCompensatedPrefixCorrection fp v (i.val + 1)
            (Nat.succ_le_of_lt i.isLt) j|
        ≤ ∑ i : Fin n, (10 / 9 : ℝ) * ((i.val : ℝ) * fp.u) * S := hsum
    _ = (10 / 9 : ℝ) * fp.u * S *
          ∑ i : Fin n, (i.val : ℝ) := hsum_simplified
    _ ≤ (10 / 9 : ℝ) * fp.u * S * ((n : ℝ) ^ 2 / 2) := hweighted
    _ = (5 / 9 : ℝ) * ((n : ℝ) ^ 2 * fp.u) *
          ∑ i : Fin n, |v i| := by
      simp [S]
      ring

/-- Exact correction-prefix aggregate in the form required by the self-term
absorption lemma. -/
theorem alternativeCompensatedCorrectionExactPrefixes_abs_sum_le_nine_tenths_n_sq_u
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 10) :
    ∑ i : Fin n,
        |∑ j : Fin (i.val + 1),
          alternativeCompensatedPrefixCorrection fp v (i.val + 1)
            (Nat.succ_le_of_lt i.isLt) j| ≤
      (9 / 10 : ℝ) * ((n : ℝ) ^ 2 * fp.u) *
        ∑ i : Fin n, |v i| := by
  have hbase_nonneg :
      0 ≤ ((n : ℝ) ^ 2 * fp.u) * ∑ i : Fin n, |v i| := by
    exact mul_nonneg
      (mul_nonneg (sq_nonneg (n : ℝ)) fp.u_nonneg)
      (Finset.sum_nonneg fun i _hi => abs_nonneg (v i))
  exact le_trans
    (alternativeCompensatedCorrectionExactPrefixes_abs_sum_le_five_ninth_n_sq_u
      fp n v hexact hsmall)
    (by nlinarith)

/-- Fully proved running-error budget for the correction list in the
alternative compensated-summation equation-(4.10) route. -/
theorem alternativeCompensatedCorrectionRunningErrorBudget_of_exact_steps
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 10) :
    fp.u *
        ∑ i : Fin n,
          |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
      ((n : ℝ) ^ 2 * fp.u ^ 2) * ∑ i : Fin n, |v i| := by
  exact
    alternativeCompensatedCorrectionRunningErrorBudget_of_exact_prefix_budget
      fp n v hsmall
      (alternativeCompensatedCorrectionExactPrefixes_abs_sum_le_nine_tenths_n_sq_u
        fp n v hexact hsmall)

/-- If each local correction formula is exact, the recursive accumulation of
stored corrections is exact, and the final main-plus-correction add is exact,
then the p. 94 alternative compensated-summation value equals the exact source
sum. -/
theorem fl_alternativeCompensatedSum_eq_sum_of_exact_steps_and_exact_correction_sum
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hglobal :
      fl_alternativeCompensatedGlobalCorrection fp n v =
        ∑ i : Fin n, alternativeCompensatedCorrections fp v i)
    (hfinal :
      fp.fl_add (fl_alternativeCompensatedMainSum fp n v)
          (fl_alternativeCompensatedGlobalCorrection fp n v) =
        fl_alternativeCompensatedMainSum fp n v +
          fl_alternativeCompensatedGlobalCorrection fp n v) :
    fl_alternativeCompensatedSum fp n v = ∑ i : Fin n, v i := by
  rw [fl_alternativeCompensatedSum_eq_add_globalCorrection, hfinal, hglobal]
  exact
    fl_alternativeCompensatedMainSum_add_exact_corrections_eq_sum_of_exact_steps
      fp n v hexact

/-- Under exact arithmetic, the main sum in the p. 94 alternative compensated
variant is the exact source sum. -/
theorem fl_alternativeCompensatedMainSum_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) :
    ∀ (n : ℕ) (v : Fin n → ℝ),
      fl_alternativeCompensatedMainSum
          (FPModel.exactWithUnitRoundoff u0 hu0) n v =
        ∑ i : Fin n, v i
  | 0, _v => by
      simp [fl_alternativeCompensatedMainSum,
        alternativeCompensatedPrefixSum]
  | n + 1, v => by
      let fp := FPModel.exactWithUnitRoundoff u0 hu0
      have hfold :
          fl_alternativeCompensatedMainSum fp (n + 1) v =
            (alternativeCompensatedStepTrace fp (v (Fin.last n))
              (fl_alternativeCompensatedMainSum fp n
                (fun i : Fin n => v i.castSucc))).nextSum := by
        unfold fl_alternativeCompensatedMainSum
          alternativeCompensatedPrefixSum
        rw [Fin.foldl_succ_last]
      rw [hfold,
        fl_alternativeCompensatedMainSum_exactWithUnitRoundoff u0 hu0 n
          (fun i : Fin n => v i.castSucc)]
      simp [fp, alternativeCompensatedStepTrace,
        AlternativeCompensatedStepTrace.nextSum,
        FPModel.exactWithUnitRoundoff, Fin.sum_univ_castSucc, add_comm]

/-- Under exact arithmetic, every stored local correction in the p. 94
alternative variant is zero. -/
theorem alternativeCompensatedCorrections_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) {n : ℕ} (v : Fin n → ℝ) :
    ∀ i : Fin n,
      alternativeCompensatedCorrections
          (FPModel.exactWithUnitRoundoff u0 hu0) v i = 0 := by
  intro i
  simp [alternativeCompensatedCorrections, alternativeCompensatedTrace,
    alternativeCompensatedStepTrace, FPModel.exactWithUnitRoundoff]

/-- Under exact arithmetic, the recursively accumulated global correction in
the p. 94 alternative variant is zero. -/
theorem fl_alternativeCompensatedGlobalCorrection_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) (n : ℕ) (v : Fin n → ℝ) :
    fl_alternativeCompensatedGlobalCorrection
        (FPModel.exactWithUnitRoundoff u0 hu0) n v = 0 := by
  rw [fl_alternativeCompensatedGlobalCorrection_eq_recursiveSum]
  rw [fl_recursiveSum_exactWithUnitRoundoff]
  simp [alternativeCompensatedCorrections_exactWithUnitRoundoff u0 hu0 v]

/-- Under exact arithmetic, the p. 94 alternative compensated-summation
variant returns the exact source sum. -/
theorem fl_alternativeCompensatedSum_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) (n : ℕ) (v : Fin n → ℝ) :
    fl_alternativeCompensatedSum
        (FPModel.exactWithUnitRoundoff u0 hu0) n v =
      ∑ i : Fin n, v i := by
  rw [fl_alternativeCompensatedSum_eq_add_globalCorrection,
    fl_alternativeCompensatedMainSum_exactWithUnitRoundoff u0 hu0,
    fl_alternativeCompensatedGlobalCorrection_exactWithUnitRoundoff u0 hu0]
  simp [FPModel.exactWithUnitRoundoff]

/-- Higham, 2nd ed., Chapter 4, Section 4.3, equation (4.10) transfer layer.

For the p. 94 alternative compensated-summation variant, the local exact
correction invariant reduces the source-shaped backward-error theorem to one
remaining correction-transfer obligation.  If the recursive summation error on
the stored correction list can be rewritten as source perturbations bounded by
`C`, then the final rounded add gives source perturbations bounded by
`fp.u + C + C*fp.u`.

This is intentionally an intermediate theorem: the source-strength row still
requires a proof of the displayed correction-transfer bound with
`C = O(n^2*u^2)`. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_transfer
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1))
    {C : ℝ} (hC_nonneg : 0 ≤ C)
    (htransfer :
      ∀ θ : Fin n → ℝ,
        (∀ i, |θ i| ≤ gamma fp (n - 1)) →
        ∃ η : Fin n → ℝ,
          (∀ i, |η i| ≤ C) ∧
          (∑ i : Fin n,
              alternativeCompensatedCorrections fp v i * θ i) =
            ∑ i : Fin n, v i * η i) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ fp.u + C + C * fp.u) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  let corr : Fin n → ℝ := alternativeCompensatedCorrections fp v
  let main := fl_alternativeCompensatedMainSum fp n v
  let global := fl_alternativeCompensatedGlobalCorrection fp n v
  let source := ∑ i : Fin n, v i
  let exactCorr := ∑ i : Fin n, corr i
  obtain ⟨θ, hθ, hglobalBack⟩ :=
    recursiveSum_backward_error fp n corr hgamma
  obtain ⟨η, hη, hcorrTransfer⟩ := htransfer θ hθ
  obtain ⟨δ, hδ, hfinal⟩ := fp.model_add main global
  have hmain :
      main + exactCorr = source := by
    simpa [main, exactCorr, source, corr] using
      fl_alternativeCompensatedMainSum_add_exact_corrections_eq_sum_of_exact_steps
        fp n v hexact
  have hglobalErr :
      global - exactCorr = ∑ i : Fin n, corr i * θ i := by
    simpa [global, exactCorr, corr, fl_alternativeCompensatedGlobalCorrection]
      using recursiveSum_error_decomp fp n corr θ hglobalBack
  have hglobalSource :
      global = exactCorr + ∑ i : Fin n, v i * η i := by
    have hglobal_eq :
        global = exactCorr + ∑ i : Fin n, corr i * θ i := by
      linarith
    calc
      global = exactCorr + ∑ i : Fin n, corr i * θ i := hglobal_eq
      _ = exactCorr + ∑ i : Fin n, v i * η i := by
        rw [hcorrTransfer]
  have hmainGlobalSource :
      main + global = ∑ i : Fin n, v i * (1 + η i) := by
    calc
      main + global = source + ∑ i : Fin n, v i * η i := by
        rw [hglobalSource]
        linarith
      _ = ∑ i : Fin n, v i * (1 + η i) := by
        dsimp [source]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
  refine ⟨fun i => η i + δ + η i * δ, ?_, ?_⟩
  · intro i
    have hmul : |η i * δ| ≤ C * fp.u := by
      rw [abs_mul]
      exact mul_le_mul (hη i) hδ (abs_nonneg δ) hC_nonneg
    calc
      |η i + δ + η i * δ|
          ≤ |η i + δ| + |η i * δ| := abs_add_le _ _
      _ ≤ (|η i| + |δ|) + |η i * δ| := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right (abs_add_le (η i) δ) |η i * δ|
      _ ≤ (C + fp.u) + C * fp.u := by
        exact add_le_add (add_le_add (hη i) hδ) hmul
      _ = fp.u + C + C * fp.u := by ring
  · calc
      fl_alternativeCompensatedSum fp n v = fp.fl_add main global := by
        simpa [main, global] using
          fl_alternativeCompensatedSum_eq_add_globalCorrection fp n v
      _ = (main + global) * (1 + δ) := hfinal
      _ = (∑ i : Fin n, v i * (1 + η i)) * (1 + δ) := by
        rw [hmainGlobalSource]
      _ = ∑ i : Fin n, v i * (1 + (η i + δ + η i * δ)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _hi
        ring

/-- Capped form of
`fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_transfer`.

This is the equation-(4.10) handoff shape: once a source proof supplies a
correction-transfer radius `C` and an arithmetic budget `fp.u + C + C*fp.u ≤ B`,
the alternative compensated-summation value has a source-shaped backward-error
witness bounded by `B`. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_transfer_le
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1))
    {B C : ℝ} (hC_nonneg : 0 ≤ C)
    (htransfer :
      ∀ θ : Fin n → ℝ,
        (∀ i, |θ i| ≤ gamma fp (n - 1)) →
        ∃ η : Fin n → ℝ,
          (∀ i, |η i| ≤ C) ∧
          (∑ i : Fin n,
              alternativeCompensatedCorrections fp v i * θ i) =
            ∑ i : Fin n, v i * η i)
    (hbudget : fp.u + C + C * fp.u ≤ B) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ B) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  obtain ⟨μ, hμ, hsum⟩ :=
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_transfer
      fp n v hexact hgamma hC_nonneg htransfer
  exact ⟨μ, fun i => le_trans (hμ i) hbudget, hsum⟩

/-- Absolute correction-list bound implies the correction-transfer obligation
used by equation-(4.10)'s alternative compensated-summation bridge.

If the stored local corrections have absolute sum at most
`D * sum_i |x_i|`, then the recursive-summation error on those corrections is
source-representable with radius `gamma (n-1) * D`. -/
theorem alternativeCompensatedCorrectionTransfer_of_correction_abs_sum_le
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hgamma : gammaValid fp (n - 1))
    {D : ℝ} (hD_nonneg : 0 ≤ D)
    (hcorrAbs :
      ∑ i : Fin n, |alternativeCompensatedCorrections fp v i| ≤
        D * ∑ i : Fin n, |v i|) :
    ∀ θ : Fin n → ℝ,
      (∀ i, |θ i| ≤ gamma fp (n - 1)) →
      ∃ η : Fin n → ℝ,
        (∀ i, |η i| ≤ gamma fp (n - 1) * D) ∧
        (∑ i : Fin n,
            alternativeCompensatedCorrections fp v i * θ i) =
          ∑ i : Fin n, v i * η i := by
  intro θ hθ
  let corr : Fin n → ℝ := alternativeCompensatedCorrections fp v
  have hgamma_nonneg : 0 ≤ gamma fp (n - 1) :=
    gamma_nonneg fp hgamma
  have hC_nonneg : 0 ≤ gamma fp (n - 1) * D :=
    mul_nonneg hgamma_nonneg hD_nonneg
  have habs :
      |∑ i : Fin n, corr i * θ i| ≤
        (gamma fp (n - 1) * D) * ∑ i : Fin n, |v i| := by
    calc
      |∑ i : Fin n, corr i * θ i|
          ≤ ∑ i : Fin n, |corr i * θ i| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin n, |corr i| * |θ i| := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [abs_mul]
      _ ≤ ∑ i : Fin n, |corr i| * gamma fp (n - 1) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact mul_le_mul_of_nonneg_left (hθ i) (abs_nonneg (corr i))
      _ = gamma fp (n - 1) * ∑ i : Fin n, |corr i| := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ gamma fp (n - 1) *
            (D * ∑ i : Fin n, |v i|) := by
        exact mul_le_mul_of_nonneg_left (by simpa [corr] using hcorrAbs)
          hgamma_nonneg
      _ = (gamma fp (n - 1) * D) *
            ∑ i : Fin n, |v i| := by ring
  simpa [corr] using
    exists_summation_source_coefficients_of_abs_le_mul_sum_abs
      v hC_nonneg habs

/-- Equation-(4.10) composition from an absolute bound on the stored correction
list.

The remaining source proof obligation is now the interpretable inequality
`sum_i |e_i| <= D * sum_i |x_i|`; recursive summation of the correction list
then contributes the radius `gamma (n-1) * D`, and the final rounded add
contributes the outer `fp.u` term. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_abs_sum_le
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1))
    {D : ℝ} (hD_nonneg : 0 ≤ D)
    (hcorrAbs :
      ∑ i : Fin n, |alternativeCompensatedCorrections fp v i| ≤
        D * ∑ i : Fin n, |v i|) :
    ∃ μ : Fin n → ℝ,
      (∀ i,
        |μ i| ≤
          fp.u + gamma fp (n - 1) * D +
            (gamma fp (n - 1) * D) * fp.u) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_transfer
      fp n v hexact hgamma
      (mul_nonneg (gamma_nonneg fp hgamma) hD_nonneg)
      (alternativeCompensatedCorrectionTransfer_of_correction_abs_sum_le
        fp n v hgamma hD_nonneg hcorrAbs)

/-- Capped version of
`fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_abs_sum_le`.

This is the natural finite-budget handoff for the printed equation-(4.10)
constant: prove a correction-list absolute-sum bound with radius `D`, prove the
displayed arithmetic cap `fp.u + gamma(n-1)*D + gamma(n-1)*D*fp.u <= B`, and
this theorem supplies the final source-shaped backward-error witness. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_abs_sum_le_budget
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1))
    {B D : ℝ} (hD_nonneg : 0 ≤ D)
    (hcorrAbs :
      ∑ i : Fin n, |alternativeCompensatedCorrections fp v i| ≤
        D * ∑ i : Fin n, |v i|)
    (hbudget :
      fp.u + gamma fp (n - 1) * D +
          (gamma fp (n - 1) * D) * fp.u ≤ B) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ B) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  obtain ⟨μ, hμ, hsum⟩ :=
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_abs_sum_le
      fp n v hexact hgamma hD_nonneg hcorrAbs
  exact ⟨μ, fun i => le_trans (hμ i) hbudget, hsum⟩

/-- Pointwise local-budget form for the stored corrections in the p. 94
alternative compensated-summation variant.

When the local correction formula is exact, the stored correction `e_i` is
exactly the residual of the main rounded add `s_i = fl(temp_i + x_i)`, up to
sign.  Thus any absolute budget for that main-add residual is also a budget for
`|e_i|`. -/
theorem alternativeCompensatedCorrection_abs_le_of_exact_step_and_main_add_residual
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hexact_i :
      let sum := alternativeCompensatedPrefixSum fp v i.val
        (Nat.le_of_lt i.isLt)
      let trace := alternativeCompensatedStepTrace fp (v i) sum
      CorrectionFormulaTrace.exact sum (v i)
        ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    {B : ℝ}
    (hmain :
      |(alternativeCompensatedTrace fp v i).s -
          ((alternativeCompensatedTrace fp v i).temp + v i)| ≤ B) :
    |alternativeCompensatedCorrections fp v i| ≤ B := by
  let sum := alternativeCompensatedPrefixSum fp v i.val
    (Nat.le_of_lt i.isLt)
  let trace := alternativeCompensatedStepTrace fp (v i) sum
  have hcorr :
      sum + v i = trace.s + trace.e := by
    simpa [CorrectionFormulaTrace.exact, sum, trace] using hexact_i
  have he :
      trace.e = sum + v i - trace.s := by
    linarith
  calc
    |alternativeCompensatedCorrections fp v i| = |trace.e| := by
      simp [alternativeCompensatedCorrections, alternativeCompensatedTrace,
        trace, sum]
    _ = |sum + v i - trace.s| := by rw [he]
    _ = |trace.s - (sum + v i)| := by rw [abs_sub_comm]
    _ =
        |(alternativeCompensatedTrace fp v i).s -
          ((alternativeCompensatedTrace fp v i).temp + v i)| := by
      simp [alternativeCompensatedTrace, alternativeCompensatedStepTrace,
        trace, sum]
    _ ≤ B := hmain

/-- The primitive `FPModel` add model gives the local main-add residual budget
used by the alternative compensated-summation correction analysis. -/
theorem alternativeCompensatedTrace_main_add_residual_le_unit_roundoff
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |(alternativeCompensatedTrace fp v i).s -
        ((alternativeCompensatedTrace fp v i).temp + v i)| ≤
      fp.u * |(alternativeCompensatedTrace fp v i).temp + v i| := by
  let trace := alternativeCompensatedTrace fp v i
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add trace.temp (v i)
  have hs : trace.s = fp.fl_add trace.temp (v i) := by
    simp [trace, alternativeCompensatedTrace, alternativeCompensatedStepTrace]
  have hres :
      |trace.s - (trace.temp + v i)| ≤ fp.u * |trace.temp + v i| := by
    calc
      |trace.s - (trace.temp + v i)|
          = |(trace.temp + v i) * δ| := by
            rw [hs, hfl]
            ring_nf
      _ = |trace.temp + v i| * |δ| := by
        rw [abs_mul]
      _ ≤ |trace.temp + v i| * fp.u := by
        exact mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
      _ = fp.u * |trace.temp + v i| := by ring
  simpa [trace] using hres

/-- Local main-add residual budgets imply an absolute bound on the stored
correction list for the p. 94 alternative compensated-summation variant. -/
theorem alternativeCompensatedCorrections_abs_sum_le_of_local_main_add_residual_budget
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    {B : Fin n → ℝ}
    (hmain :
      ∀ i : Fin n,
        |(alternativeCompensatedTrace fp v i).s -
            ((alternativeCompensatedTrace fp v i).temp + v i)| ≤ B i) :
    ∑ i : Fin n, |alternativeCompensatedCorrections fp v i| ≤
      ∑ i : Fin n, B i := by
  apply Finset.sum_le_sum
  intro i _hi
  exact
    alternativeCompensatedCorrection_abs_le_of_exact_step_and_main_add_residual
      fp v i (hexact i) (hmain i)

/-- Exact local correction formulas plus the primitive `FPModel` add model give
an absolute-sum correction bound in terms of the rounded main-add inputs. -/
theorem alternativeCompensatedCorrections_abs_sum_le_unit_roundoff_main_add_inputs
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace)) :
    ∑ i : Fin n, |alternativeCompensatedCorrections fp v i| ≤
      ∑ i : Fin n,
        fp.u * |(alternativeCompensatedTrace fp v i).temp + v i| := by
  exact
    alternativeCompensatedCorrections_abs_sum_le_of_local_main_add_residual_budget
      fp v hexact
      (fun i => alternativeCompensatedTrace_main_add_residual_le_unit_roundoff
        fp v i)

/-- Higham §4.2 running-sum form of the correction-list absolute bound:
under exact local correction formulas, the sum of stored correction magnitudes
is bounded by `u` times the sum of ordinary recursive-summation pre-rounding
partial sums. -/
theorem alternativeCompensatedCorrections_abs_sum_le_unit_roundoff_partialSums
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace)) :
    ∑ i : Fin n, |alternativeCompensatedCorrections fp v i| ≤
      fp.u * ∑ i : Fin n, |fl_partialSums fp v i| := by
  calc
    ∑ i : Fin n, |alternativeCompensatedCorrections fp v i|
        ≤ ∑ i : Fin n,
            fp.u * |(alternativeCompensatedTrace fp v i).temp + v i| :=
          alternativeCompensatedCorrections_abs_sum_le_unit_roundoff_main_add_inputs
            fp v hexact
    _ = fp.u * ∑ i : Fin n, |fl_partialSums fp v i| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [alternativeCompensatedTrace_main_add_input_eq_fl_partialSums]

/-- Local residual budgets plus an aggregate source-weighted cap close the
correction-list absolute-sum obligation used by the equation-(4.10) bridge. -/
theorem alternativeCompensatedCorrections_abs_sum_le_of_local_main_add_residual_budget_cap
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    {B : Fin n → ℝ} {D : ℝ}
    (hmain :
      ∀ i : Fin n,
        |(alternativeCompensatedTrace fp v i).s -
            ((alternativeCompensatedTrace fp v i).temp + v i)| ≤ B i)
    (hbudget :
      ∑ i : Fin n, B i ≤ D * ∑ i : Fin n, |v i|) :
    ∑ i : Fin n, |alternativeCompensatedCorrections fp v i| ≤
      D * ∑ i : Fin n, |v i| := by
  exact le_trans
    (alternativeCompensatedCorrections_abs_sum_le_of_local_main_add_residual_budget
      fp v hexact hmain)
    hbudget

/-- Unit-roundoff local residuals plus an aggregate source-weighted cap close
the correction-list absolute-sum obligation used by the equation-(4.10)
bridge.  The remaining cap is a prefix-growth/source-weighted estimate for the
rounded main-add inputs. -/
theorem alternativeCompensatedCorrections_abs_sum_le_of_unit_roundoff_main_add_inputs_cap
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    {D : ℝ}
    (hbudget :
      ∑ i : Fin n,
          fp.u * |(alternativeCompensatedTrace fp v i).temp + v i| ≤
        D * ∑ i : Fin n, |v i|) :
    ∑ i : Fin n, |alternativeCompensatedCorrections fp v i| ≤
      D * ∑ i : Fin n, |v i| := by
  exact le_trans
    (alternativeCompensatedCorrections_abs_sum_le_unit_roundoff_main_add_inputs
      fp v hexact)
    hbudget

/-- A source-weighted cap on the recursive-summation partial sums closes the
correction-list absolute-sum obligation for equation (4.10). -/
theorem alternativeCompensatedCorrections_abs_sum_le_of_partialSums_cap
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    {D : ℝ}
    (hbudget :
      fp.u * ∑ i : Fin n, |fl_partialSums fp v i| ≤
        D * ∑ i : Fin n, |v i|) :
    ∑ i : Fin n, |alternativeCompensatedCorrections fp v i| ≤
      D * ∑ i : Fin n, |v i| := by
  exact le_trans
    (alternativeCompensatedCorrections_abs_sum_le_unit_roundoff_partialSums
      fp v hexact)
    hbudget

/-- Fully instantiated correction-list absolute-sum bound using the ordinary
recursive-summation partial-sum cap. -/
theorem alternativeCompensatedCorrections_abs_sum_le_unit_roundoff_global_gamma
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1)) :
    ∑ i : Fin n, |alternativeCompensatedCorrections fp v i| ≤
      (fp.u * ((n : ℝ) * (1 + gamma fp (n - 1)))) *
        ∑ i : Fin n, |v i| := by
  have hpartial :=
    fl_partialSums_abs_sum_le_n_mul_one_add_gamma_mul_sum_abs fp n v hgamma
  calc
    ∑ i : Fin n, |alternativeCompensatedCorrections fp v i|
        ≤ fp.u * ∑ i : Fin n, |fl_partialSums fp v i| :=
          alternativeCompensatedCorrections_abs_sum_le_unit_roundoff_partialSums
            fp v hexact
    _ ≤ fp.u *
          (((n : ℝ) * (1 + gamma fp (n - 1))) *
            ∑ i : Fin n, |v i|) := by
      exact mul_le_mul_of_nonneg_left hpartial fp.u_nonneg
    _ = (fp.u * ((n : ℝ) * (1 + gamma fp (n - 1)))) *
          ∑ i : Fin n, |v i| := by ring

/-- Equation-(4.10) bridge from local main-add residual budgets.

This theorem replaces the correction-list absolute-sum hypothesis by the next
local obligation: bound each main rounded add residual and show that the sum of
those local budgets is at most `D * sum_i |x_i|`. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_local_main_add_residual_budget
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1))
    {B : Fin n → ℝ} {D : ℝ} (hD_nonneg : 0 ≤ D)
    (hmain :
      ∀ i : Fin n,
        |(alternativeCompensatedTrace fp v i).s -
            ((alternativeCompensatedTrace fp v i).temp + v i)| ≤ B i)
    (hbudget :
      ∑ i : Fin n, B i ≤ D * ∑ i : Fin n, |v i|) :
    ∃ μ : Fin n → ℝ,
      (∀ i,
        |μ i| ≤
          fp.u + gamma fp (n - 1) * D +
            (gamma fp (n - 1) * D) * fp.u) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_abs_sum_le
      fp n v hexact hgamma hD_nonneg
      (alternativeCompensatedCorrections_abs_sum_le_of_local_main_add_residual_budget_cap
        fp v hexact hmain hbudget)

/-- Capped source-shaped backward-error theorem from local main-add residual
budgets for the p. 94 alternative compensated-summation variant. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_local_main_add_residual_budget_cap
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1))
    {A : ℝ} {B : Fin n → ℝ} {D : ℝ} (hD_nonneg : 0 ≤ D)
    (hmain :
      ∀ i : Fin n,
        |(alternativeCompensatedTrace fp v i).s -
            ((alternativeCompensatedTrace fp v i).temp + v i)| ≤ B i)
    (hbudget :
      ∑ i : Fin n, B i ≤ D * ∑ i : Fin n, |v i|)
    (hcap :
      fp.u + gamma fp (n - 1) * D +
          (gamma fp (n - 1) * D) * fp.u ≤ A) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ A) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  obtain ⟨μ, hμ, hsum⟩ :=
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_local_main_add_residual_budget
      fp n v hexact hgamma hD_nonneg hmain hbudget
  exact ⟨μ, fun i => le_trans (hμ i) hcap, hsum⟩

/-- Equation-(4.10) bridge with the primitive `FPModel` local add residual
instantiated.  The remaining source-specific obligation is the aggregate cap
on `sum_i fp.u * |temp_i + x_i|`. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_unit_roundoff_main_add_inputs_cap
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1))
    {A D : ℝ} (hD_nonneg : 0 ≤ D)
    (hbudget :
      ∑ i : Fin n,
          fp.u * |(alternativeCompensatedTrace fp v i).temp + v i| ≤
        D * ∑ i : Fin n, |v i|)
    (hcap :
      fp.u + gamma fp (n - 1) * D +
          (gamma fp (n - 1) * D) * fp.u ≤ A) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ A) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_abs_sum_le_budget
      fp n v hexact hgamma hD_nonneg
      (alternativeCompensatedCorrections_abs_sum_le_of_unit_roundoff_main_add_inputs_cap
        fp v hexact hbudget)
      hcap

/-- Equation-(4.10) bridge with the correction-list budget reduced to the
ordinary recursive-summation partial-sum cap from Higham §4.2. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_partialSums_cap
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1))
    {A D : ℝ} (hD_nonneg : 0 ≤ D)
    (hbudget :
      fp.u * ∑ i : Fin n, |fl_partialSums fp v i| ≤
        D * ∑ i : Fin n, |v i|)
    (hcap :
      fp.u + gamma fp (n - 1) * D +
          (gamma fp (n - 1) * D) * fp.u ≤ A) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ A) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_abs_sum_le_budget
      fp n v hexact hgamma hD_nonneg
      (alternativeCompensatedCorrections_abs_sum_le_of_partialSums_cap
        fp v hexact hbudget)
      hcap

/-- Equation-(4.10) bridge using the running-error bound for the recursively
summed correction list.

This avoids the `gamma * sum_i |e_i|` transfer used by
`fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_abs_sum_le`.
Instead, it asks for the sharper source-weighted bound on the recursive
summation running-error budget of the stored corrections:
`u * sum_i |partial_corrections_i| <= C * sum_i |x_i|`. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_budget
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    {C : ℝ} (hC_nonneg : 0 ≤ C)
    (hbudget :
      fp.u *
          ∑ i : Fin n,
            |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
        C * ∑ i : Fin n, |v i|) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ fp.u + C + C * fp.u) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  let corr : Fin n → ℝ := alternativeCompensatedCorrections fp v
  let main := fl_alternativeCompensatedMainSum fp n v
  let global := fl_alternativeCompensatedGlobalCorrection fp n v
  let source := ∑ i : Fin n, v i
  let exactCorr := ∑ i : Fin n, corr i
  have hmain :
      main + exactCorr = source := by
    simpa [main, exactCorr, source, corr] using
      fl_alternativeCompensatedMainSum_add_exact_corrections_eq_sum_of_exact_steps
        fp n v hexact
  have hglobalErrAbs :
      |global - exactCorr| ≤ C * ∑ i : Fin n, |v i| := by
    have hrun :
        |global - exactCorr| ≤
          fp.u * ∑ i : Fin n, |fl_partialSums fp corr i| := by
      simpa [global, exactCorr, corr,
        fl_alternativeCompensatedGlobalCorrection] using
        recursiveSum_running_error_bound fp n corr
    exact le_trans hrun (by simpa [corr] using hbudget)
  obtain ⟨η, hη, hcorrTransfer⟩ :=
    exists_summation_source_coefficients_of_abs_le_mul_sum_abs
      v hC_nonneg hglobalErrAbs
  obtain ⟨δ, hδ, hfinal⟩ := fp.model_add main global
  have hglobalSource :
      global = exactCorr + ∑ i : Fin n, v i * η i := by
    have hglobal_eq :
        global = exactCorr + (global - exactCorr) := by ring
    rw [hglobal_eq, hcorrTransfer]
  have hmainGlobalSource :
      main + global = ∑ i : Fin n, v i * (1 + η i) := by
    calc
      main + global = source + ∑ i : Fin n, v i * η i := by
        rw [hglobalSource]
        linarith
      _ = ∑ i : Fin n, v i * (1 + η i) := by
        dsimp [source]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
  refine ⟨fun i => η i + δ + η i * δ, ?_, ?_⟩
  · intro i
    have hmul : |η i * δ| ≤ C * fp.u := by
      rw [abs_mul]
      exact mul_le_mul (hη i) hδ (abs_nonneg δ) hC_nonneg
    calc
      |η i + δ + η i * δ|
          ≤ |η i + δ| + |η i * δ| := abs_add_le _ _
      _ ≤ |η i| + |δ| + |η i * δ| := by
        nlinarith [abs_add_le (η i) δ]
      _ ≤ C + fp.u + C * fp.u := by
        nlinarith [hη i, hδ, hmul]
      _ = fp.u + C + C * fp.u := by ring
  · rw [fl_alternativeCompensatedSum_eq_add_globalCorrection]
    have hadd :
        fp.fl_add main global =
          (main + global) * (1 + δ) := hfinal
    rw [hadd, hmainGlobalSource]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    ring

/-- Capped version of
`fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_budget`. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_budget_cap
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    {A C : ℝ} (hC_nonneg : 0 ≤ C)
    (hbudget :
      fp.u *
          ∑ i : Fin n,
            |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
        C * ∑ i : Fin n, |v i|)
    (hcap : fp.u + C + C * fp.u ≤ A) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ A) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  obtain ⟨μ, hμ, hsum⟩ :=
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_budget
      fp n v hexact hC_nonneg hbudget
  exact ⟨μ, fun i => le_trans (hμ i) hcap, hsum⟩

/-- Equation-(4.10) printed-cap bridge from a source-weighted running-error
budget for the recursively summed correction list.

The remaining mathematical obligation is the displayed `hbudget`, whose shape
matches the running-error route: the sum of correction-summation partial sums
must be second order, bounded by `n^2*u^2 * sum_i |x_i|`. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_higham_cap
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 10)
    (hbudget :
      fp.u *
          ∑ i : Fin n,
            |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
        ((n : ℝ) ^ 2 * fp.u ^ 2) * ∑ i : Fin n, |v i|) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ 2 * fp.u + (n : ℝ) ^ 2 * fp.u ^ 2) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  have hC_nonneg : 0 ≤ (n : ℝ) ^ 2 * fp.u ^ 2 := by
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hC_le_one : (n : ℝ) ^ 2 * fp.u ^ 2 ≤ 1 := by
    have ha_nonneg : 0 ≤ (n : ℝ) * fp.u := by
      exact mul_nonneg (by exact_mod_cast Nat.zero_le n) fp.u_nonneg
    have hsq : ((n : ℝ) * fp.u) ^ 2 ≤ (1 / 10 : ℝ) ^ 2 :=
      sq_le_sq' (by nlinarith [ha_nonneg]) hsmall
    have hCeq : (n : ℝ) ^ 2 * fp.u ^ 2 = ((n : ℝ) * fp.u) ^ 2 := by
      ring
    rw [hCeq]
    nlinarith
  have hcap :
      fp.u + (n : ℝ) ^ 2 * fp.u ^ 2 +
          ((n : ℝ) ^ 2 * fp.u ^ 2) * fp.u ≤
        2 * fp.u + (n : ℝ) ^ 2 * fp.u ^ 2 := by
    have hmul :
        ((n : ℝ) ^ 2 * fp.u ^ 2) * fp.u ≤ fp.u :=
      by
        simpa [one_mul] using
          mul_le_mul_of_nonneg_right hC_le_one fp.u_nonneg
    nlinarith
  exact
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_budget_cap
      fp n v hexact hC_nonneg hbudget hcap

/-- Higham Chapter 4 equation (4.10) for the p. 94 alternative compensated
summation variant, with the correction-list running-error budget discharged
from the exact local correction formulas and `n*u <= 0.1`. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_higham_cap
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 10) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ 2 * fp.u + (n : ℝ) ^ 2 * fp.u ^ 2) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_higham_cap
      fp n v hexact hsmall
      (alternativeCompensatedCorrectionRunningErrorBudget_of_exact_steps
        fp n v hexact hsmall)

/-- Pointwise correction-partial form of the remaining equation-(4.10)
running-error budget.

If every pre-rounding partial sum formed while recursively summing the stored
corrections is bounded by `n*u*sum_i |x_i|`, then the aggregate running-error
budget required by
`fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_higham_cap`
has exactly the printed second-order size `n^2*u^2*sum_i |x_i|`. -/
theorem alternativeCompensatedCorrectionRunningErrorBudget_of_pointwise_partialSums
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hpartial :
      ∀ i : Fin n,
        |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
          ((n : ℝ) * fp.u) * ∑ j : Fin n, |v j|) :
    fp.u *
        ∑ i : Fin n,
          |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
      ((n : ℝ) ^ 2 * fp.u ^ 2) * ∑ j : Fin n, |v j| := by
  have hsum :
      ∑ i : Fin n,
          |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
        ∑ i : Fin n, ((n : ℝ) * fp.u) * ∑ j : Fin n, |v j| := by
    apply Finset.sum_le_sum
    intro i _hi
    exact hpartial i
  calc
    fp.u *
        ∑ i : Fin n,
          |fl_partialSums fp (alternativeCompensatedCorrections fp v) i|
        ≤ fp.u *
            ∑ i : Fin n, ((n : ℝ) * fp.u) * ∑ j : Fin n, |v j| := by
          exact mul_le_mul_of_nonneg_left hsum fp.u_nonneg
    _ = ((n : ℝ) ^ 2 * fp.u ^ 2) * ∑ j : Fin n, |v j| := by
          rw [Finset.sum_const]
          simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

/-- Equation-(4.10) printed-cap bridge from a pointwise bound on the computed
partial sums of the stored correction list.

This is the next dependency-reduction form after the running-error bridge: the
remaining mathematical task is to prove the displayed `hpartial` bound from
the exact local correction formulas and recursive-summation prefix analysis. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_pointwise_correction_partial_higham_cap
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 10)
    (hpartial :
      ∀ i : Fin n,
        |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
          ((n : ℝ) * fp.u) * ∑ j : Fin n, |v j|) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ 2 * fp.u + (n : ℝ) ^ 2 * fp.u ^ 2) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_higham_cap
      fp n v hexact hsmall
      (alternativeCompensatedCorrectionRunningErrorBudget_of_pointwise_partialSums
        fp n v hpartial)

/-- Equation-(4.10) source-shaped backward-error theorem with the correction
budget instantiated by the recursive-summation global partial-sum cap.

This leaves no correction-list or partial-sum hypothesis; the displayed radius
is the exact bound produced by the current local infrastructure. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_global_gamma
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1)) :
    ∃ μ : Fin n → ℝ,
      (∀ i,
        |μ i| ≤
          fp.u +
            gamma fp (n - 1) *
              (fp.u * ((n : ℝ) * (1 + gamma fp (n - 1)))) +
            (gamma fp (n - 1) *
              (fp.u * ((n : ℝ) * (1 + gamma fp (n - 1))))) * fp.u) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  have hD_nonneg :
      0 ≤ fp.u * ((n : ℝ) * (1 + gamma fp (n - 1))) := by
    have hfactor : 0 ≤ (n : ℝ) * (1 + gamma fp (n - 1)) := by
      exact mul_nonneg (by exact_mod_cast Nat.zero_le n)
        (by nlinarith [gamma_nonneg fp hgamma])
    exact mul_nonneg fp.u_nonneg hfactor
  exact
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_abs_sum_le
      fp n v hexact hgamma hD_nonneg
      (alternativeCompensatedCorrections_abs_sum_le_unit_roundoff_global_gamma
        fp n v hexact hgamma)

/-- Capped version of
`fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_global_gamma`. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_global_gamma_cap
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1))
    {A : ℝ}
    (hcap :
      fp.u +
          gamma fp (n - 1) *
            (fp.u * ((n : ℝ) * (1 + gamma fp (n - 1)))) +
          (gamma fp (n - 1) *
            (fp.u * ((n : ℝ) * (1 + gamma fp (n - 1))))) * fp.u ≤ A) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ A) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  obtain ⟨μ, hμ, hsum⟩ :=
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_global_gamma
      fp n v hexact hgamma
  exact ⟨μ, fun i => le_trans (hμ i) hcap, hsum⟩

/-- The instantiated global-gamma route for equation (4.10) is not by itself
strong enough to imply the printed `2*u + n^2*u^2` cap from only
`n*u <= 0.1`.

This is a route audit, not a counterexample to Higham's theorem: it shows that
the current partial-sum majorization has to be sharpened before the exact
printed constant can be obtained from this proof path. -/
theorem not_forall_alternativeCompensated_globalGammaRadius_le_two_u_add_n_sq_u_sq_of_nu_le_tenth :
    ¬ ∀ (fp : FPModel) (n : ℕ),
      gammaValid fp (n - 1) →
      (n : ℝ) * fp.u ≤ 1 / 10 →
      fp.u +
          gamma fp (n - 1) *
            (fp.u * ((n : ℝ) * (1 + gamma fp (n - 1)))) +
          (gamma fp (n - 1) *
            (fp.u * ((n : ℝ) * (1 + gamma fp (n - 1))))) * fp.u ≤
        2 * fp.u + (n : ℝ) ^ 2 * fp.u ^ 2 := by
  intro h
  let fp : FPModel := FPModel.exactWithUnitRoundoff (1 / 1000) (by norm_num)
  have hvalid : gammaValid fp (100 - 1) := by
    norm_num [fp, FPModel.exactWithUnitRoundoff, gammaValid]
  have hsmall : (100 : ℝ) * fp.u ≤ 1 / 10 := by
    norm_num [fp, FPModel.exactWithUnitRoundoff]
  have hineq := h fp 100 hvalid hsmall
  norm_num [fp, FPModel.exactWithUnitRoundoff, gamma] at hineq

/-- If the final p. 94 alternative compensated-summation value satisfies a
backward-error representation with componentwise perturbation bound `B`, then
it satisfies the corresponding absolute forward-error bound.  This is the
algebraic part of turning an equation-(4.10)-style witness into a forward
error statement. -/
theorem fl_alternativeCompensatedSum_forward_error_bound_of_backward
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) {B : ℝ}
    (hback :
      ∃ μ : Fin n → ℝ,
        (∀ i, |μ i| ≤ B) ∧
        fl_alternativeCompensatedSum fp n v =
          ∑ i : Fin n, v i * (1 + μ i)) :
    |fl_alternativeCompensatedSum fp n v - ∑ i : Fin n, v i| ≤
      B * ∑ i : Fin n, |v i| :=
  kahan_backward_error_forward_bound_core v hback

/-- One-signed relative-error consequence of a supplied p. 94 alternative
compensated-summation backward-error representation. -/
theorem fl_alternativeCompensatedSum_relError_le_of_backward_oneSigned
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) {B : ℝ}
    (hback :
      ∃ μ : Fin n → ℝ,
        (∀ i, |μ i| ≤ B) ∧
        fl_alternativeCompensatedSum fp n v =
          ∑ i : Fin n, v i * (1 + μ i))
    (hv : OneSigned v) (hsum : (∑ i : Fin n, v i) ≠ 0) :
    relError (fl_alternativeCompensatedSum fp n v)
        (∑ i : Fin n, v i) ≤ B := by
  have hden : 0 < |∑ i : Fin n, v i| := abs_pos.mpr hsum
  have hbound :=
    fl_alternativeCompensatedSum_forward_error_bound_of_backward
      fp n v hback
  have hbound_one :
      |fl_alternativeCompensatedSum fp n v - ∑ i : Fin n, v i| ≤
        B * |∑ i : Fin n, v i| := by
    simpa [sum_abs_eq_abs_sum_of_oneSigned v hv] using hbound
  unfold relError
  rw [div_le_iff₀ hden]
  exact hbound_one

/-! ## Kahan's modified no-guard correction -/

/-- Source-shaped predicate for `sign(x) = sign(y)` with the usual real sign
trichotomy: both negative, both zero, or both positive. -/
def kahanSameSign (x y : ℝ) : Prop :=
  (x < 0 ∧ y < 0) ∨ (x = 0 ∧ y = 0) ∨ (0 < x ∧ 0 < y)

noncomputable instance kahanSameSignDecidable (x y : ℝ) :
    Decidable (kahanSameSign x y) :=
  Classical.dec _

/-- One source-level step of Kahan's no-guard-digit modified compensated
summation trace.  The field `f0` records the explicit source assignment
`f = 0`; `f` records the value after the optional same-sign branch. -/
structure KahanModifiedNoGuardStepTrace where
  temp : ℝ
  y : ℝ
  s : ℝ
  f0 : ℝ
  f : ℝ
  e : ℝ

namespace KahanModifiedNoGuardStepTrace

/-- The persistent state after a modified no-guard Kahan step trace. -/
def nextState (t : KahanModifiedNoGuardStepTrace) : KahanState :=
  { s := t.s, e := t.e }

end KahanModifiedNoGuardStepTrace

/-- One rounded step of Kahan's modified compensated summation for the
no-guard-digit model. -/
noncomputable def kahanModifiedNoGuardStepTrace
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    KahanModifiedNoGuardStepTrace :=
  let temp := state.s
  let y := fp.fl_add x state.e
  let s := fp.fl_add temp y
  let f0 := 0
  let f :=
    if kahanSameSign temp y then
      fp.fl_add (fp.fl_sub (fp.fl_mul ((46 : ℝ) / 100) s) s) s
    else
      f0
  let e := fp.fl_add (fp.fl_sub (fp.fl_sub temp f) (fp.fl_sub s f)) y
  { temp := temp, y := y, s := s, f0 := f0, f := f, e := e }

/-- Persistent-state update induced by one modified no-guard Kahan step. -/
noncomputable def kahanModifiedNoGuardStep
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) : KahanState :=
  (kahanModifiedNoGuardStepTrace fp x state).nextState

/-- The `temp` assignment in the modified no-guard Kahan variant. -/
theorem kahanModifiedNoGuardStepTrace_temp
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    (kahanModifiedNoGuardStepTrace fp x state).temp = state.s := by
  rfl

/-- The `y = x_i + e` assignment in the modified no-guard Kahan variant. -/
theorem kahanModifiedNoGuardStepTrace_y
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    (kahanModifiedNoGuardStepTrace fp x state).y = fp.fl_add x state.e := by
  rfl

/-- The `s = temp + y` assignment in the modified no-guard Kahan variant. -/
theorem kahanModifiedNoGuardStepTrace_s
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    (kahanModifiedNoGuardStepTrace fp x state).s =
      fp.fl_add (kahanModifiedNoGuardStepTrace fp x state).temp
        (kahanModifiedNoGuardStepTrace fp x state).y := by
  rfl

/-- The explicit `f = 0` assignment before the same-sign branch. -/
theorem kahanModifiedNoGuardStepTrace_f0
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    (kahanModifiedNoGuardStepTrace fp x state).f0 = 0 := by
  rfl

/-- The same-sign branch
`if sign(temp) = sign(y), f = (0.46 * s - s) + s, end`. -/
theorem kahanModifiedNoGuardStepTrace_f
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    (kahanModifiedNoGuardStepTrace fp x state).f =
      if kahanSameSign
          (kahanModifiedNoGuardStepTrace fp x state).temp
          (kahanModifiedNoGuardStepTrace fp x state).y then
        fp.fl_add
          (fp.fl_sub
            (fp.fl_mul ((46 : ℝ) / 100)
              (kahanModifiedNoGuardStepTrace fp x state).s)
            (kahanModifiedNoGuardStepTrace fp x state).s)
          (kahanModifiedNoGuardStepTrace fp x state).s
      else
        (kahanModifiedNoGuardStepTrace fp x state).f0 := by
  rfl

/-- The modified correction assignment
`e = ((temp - f) - (s - f)) + y`, in the displayed evaluation order. -/
theorem kahanModifiedNoGuardStepTrace_e
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    (kahanModifiedNoGuardStepTrace fp x state).e =
      fp.fl_add
        (fp.fl_sub
          (fp.fl_sub (kahanModifiedNoGuardStepTrace fp x state).temp
            (kahanModifiedNoGuardStepTrace fp x state).f)
          (fp.fl_sub (kahanModifiedNoGuardStepTrace fp x state).s
            (kahanModifiedNoGuardStepTrace fp x state).f))
        (kahanModifiedNoGuardStepTrace fp x state).y := by
  rfl

/-- State after the first `k` modified no-guard Kahan steps over a
length-`n` input. -/
noncomputable def kahanModifiedNoGuardPrefixState
    (fp : NoGuardFPModel) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : KahanState :=
  Fin.foldl k
    (fun state i =>
      kahanModifiedNoGuardStep fp
        (v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) state)
    KahanState.zero

/-- The per-index modified no-guard Kahan step trace, with the input state
obtained by running all earlier steps. -/
noncomputable def kahanModifiedNoGuardTrace
    (fp : NoGuardFPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) : KahanModifiedNoGuardStepTrace :=
  kahanModifiedNoGuardStepTrace fp (v i)
    (kahanModifiedNoGuardPrefixState fp v i.val (Nat.le_of_lt i.isLt))

/-- Final modified no-guard Kahan state after processing all `n` inputs. -/
noncomputable def fl_kahanModifiedNoGuardState
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) : KahanState :=
  kahanModifiedNoGuardPrefixState fp v n (Nat.le_refl n)

/-- Final sum returned by the modified no-guard Kahan variant. -/
noncomputable def fl_kahanModifiedNoGuardSum
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  (fl_kahanModifiedNoGuardState fp n v).s

/-- Final correction term retained by the modified no-guard Kahan variant. -/
noncomputable def fl_kahanModifiedNoGuardCorrection
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  (fl_kahanModifiedNoGuardState fp n v).e

/-- The final modified no-guard state is the explicit `n`-step prefix state. -/
theorem fl_kahanModifiedNoGuardState_eq_prefixState
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanModifiedNoGuardState fp n v =
      kahanModifiedNoGuardPrefixState fp v n (Nat.le_refl n) := by
  rfl

/-- The returned modified no-guard sum is the `s` field of the final state. -/
theorem fl_kahanModifiedNoGuardSum_eq_state_s
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanModifiedNoGuardSum fp n v =
      (fl_kahanModifiedNoGuardState fp n v).s := by
  rfl

/-- The retained modified no-guard correction is the `e` field of the final
state. -/
theorem fl_kahanModifiedNoGuardCorrection_eq_state_e
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanModifiedNoGuardCorrection fp n v =
      (fl_kahanModifiedNoGuardState fp n v).e := by
  rfl

/-- In exact arithmetic, one modified no-guard Kahan step adds the new input
to the running sum and leaves a zero correction.  The same-sign branch may
compute a nonzero auxiliary `f`, but it cancels algebraically in the correction
assignment. -/
theorem kahanModifiedNoGuardStep_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 < u0) (x sum : ℝ) :
    kahanModifiedNoGuardStep
        (NoGuardFPModel.exactWithUnitRoundoff u0 hu0) x
        { s := sum, e := 0 } =
      { s := sum + x, e := 0 } := by
  by_cases hsame : kahanSameSign sum x
  · simp [kahanModifiedNoGuardStep, kahanModifiedNoGuardStepTrace,
      KahanModifiedNoGuardStepTrace.nextState,
      NoGuardFPModel.exactWithUnitRoundoff, hsame]
  · simp [kahanModifiedNoGuardStep, kahanModifiedNoGuardStepTrace,
      KahanModifiedNoGuardStepTrace.nextState,
      NoGuardFPModel.exactWithUnitRoundoff, hsame]

/-- Under exact arithmetic, Kahan's modified no-guard state is the exact source
sum with zero retained correction. -/
theorem fl_kahanModifiedNoGuardState_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 < u0) :
    ∀ (n : ℕ) (v : Fin n → ℝ),
      fl_kahanModifiedNoGuardState
          (NoGuardFPModel.exactWithUnitRoundoff u0 hu0) n v =
        { s := ∑ i : Fin n, v i, e := 0 }
  | 0, _v => by
      simp [fl_kahanModifiedNoGuardState, kahanModifiedNoGuardPrefixState,
        KahanState.zero]
  | n + 1, v => by
      let fp := NoGuardFPModel.exactWithUnitRoundoff u0 hu0
      have hfold :
          fl_kahanModifiedNoGuardState fp (n + 1) v =
            kahanModifiedNoGuardStep fp (v (Fin.last n))
              (fl_kahanModifiedNoGuardState fp n
                (fun i : Fin n => v i.castSucc)) := by
        unfold fl_kahanModifiedNoGuardState kahanModifiedNoGuardPrefixState
        rw [Fin.foldl_succ_last]
      rw [hfold, fl_kahanModifiedNoGuardState_exactWithUnitRoundoff u0 hu0 n
        (fun i : Fin n => v i.castSucc)]
      rw [kahanModifiedNoGuardStep_exactWithUnitRoundoff]
      simp [Fin.sum_univ_castSucc, add_comm]

/-- Under exact arithmetic, the modified no-guard Kahan variant returns the
exact source sum. -/
theorem fl_kahanModifiedNoGuardSum_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 < u0) (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanModifiedNoGuardSum
        (NoGuardFPModel.exactWithUnitRoundoff u0 hu0) n v =
      ∑ i : Fin n, v i := by
  have hstate :=
    fl_kahanModifiedNoGuardState_exactWithUnitRoundoff u0 hu0 n v
  simpa [fl_kahanModifiedNoGuardSum] using congrArg KahanState.s hstate

/-- Under exact arithmetic, the modified no-guard Kahan variant retains zero
correction. -/
theorem fl_kahanModifiedNoGuardCorrection_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 < u0) (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanModifiedNoGuardCorrection
        (NoGuardFPModel.exactWithUnitRoundoff u0 hu0) n v = 0 := by
  have hstate :=
    fl_kahanModifiedNoGuardState_exactWithUnitRoundoff u0 hu0 n v
  simpa [fl_kahanModifiedNoGuardCorrection] using congrArg KahanState.e hstate

end NumStability
