-- Algorithms/CompensatedSum.lean

import Mathlib.Data.Real.Basic
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

/-- The per-index Kahan step trace, with the input state obtained by running
all earlier steps. -/
noncomputable def kahanTrace (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) : KahanStepTrace :=
  kahanStepTrace fp (v i)
    (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))

/-- Final Kahan state after processing all `n` inputs. -/
noncomputable def fl_kahanState (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) : KahanState :=
  kahanPrefixState fp v n (Nat.le_refl n)

/-- Final compensated-summation value returned by Algorithm 4.2. -/
noncomputable def fl_kahanSum (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  (fl_kahanState fp n v).s

/-- Final correction term retained by Algorithm 4.2. -/
noncomputable def fl_kahanCorrection (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  (fl_kahanState fp n v).e

/-- The final state is the explicit `n`-step prefix state. -/
theorem fl_kahanState_eq_prefixState (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) :
    fl_kahanState fp n v = kahanPrefixState fp v n (Nat.le_refl n) := by
  rfl

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
