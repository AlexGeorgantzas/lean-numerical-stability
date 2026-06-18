-- Algorithms/CompensatedSum.lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Error
import LeanFpAnalysis.FP.Analysis.FloatingPointArithmetic
import LeanFpAnalysis.FP.Algorithms.RecursiveSum

namespace LeanFpAnalysis.FP

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

/-- One Algorithm 4.2 step specialized to the source-facing finite
round-to-even selector of a `FloatingPointFormat`.  This is the concrete
finite-format wrapper used for result-by-result audits such as Problem 4.9. -/
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

/-- State after the first `k` finite-format Kahan steps over a length-`n`
input. -/
noncomputable def finiteKahanPrefixState (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : KahanState :=
  Fin.foldl k
    (fun state i =>
      finiteKahanStep fmt (v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) state)
    KahanState.zero

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

/-! ### Higham Problem 4.9 / Priest six-term example -/

/-- The six-term family from Higham Problem 4.9, due to Priest.  The printed
source is `x₁ = 2^(t+1)`, `x₂ = 2^(t+1)-2`, and
`x₃ = x₄ = x₅ = x₆ = -(2^t-1)`. -/
noncomputable def problem49PriestInput (t : ℕ) : Fin 6 → ℝ :=
  fun i =>
    if i.val = 0 then (2 : ℝ) ^ (t + 1)
    else if i.val = 1 then (2 : ℝ) ^ (t + 1) - 2
    else -((2 : ℝ) ^ t - 1)

/-- Priest's six-term Problem 4.9 family has exact real sum `2`. -/
theorem problem49PriestInput_sum_eq_two (t : ℕ) :
    (∑ i : Fin 6, problem49PriestInput t i) = 2 := by
  norm_num [problem49PriestInput, Fin.sum_univ_succ]
  rw [pow_succ]
  ring_nf
  rfl

/-- The concrete IEEE-single instance in Higham Problem 4.9 uses `t = 24`. -/
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

/-- The first value `2^(24+1)` in the concrete Problem 4.9 instance is finite
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

/-- The second value `2^(24+1)-2` in the concrete Problem 4.9 instance is
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

/-- The repeated tail value `-(2^24-1)` in the concrete Problem 4.9 instance is
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

/-- Every displayed input in the concrete Problem 4.9 instance is finite in
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
round-to-even trace for Problem 4.9: the exact sum of the first two displayed
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
      exact Nat.cast_le.mpr (by native_decide)
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

end LeanFpAnalysis.FP
