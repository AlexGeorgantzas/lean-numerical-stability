-- Analysis/NonrandomRounding.lean
--
-- Exact definitions from Higham Chapter 1, Section 1.17.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.FloatingPoint.Model

namespace NumStability

/-!
# Rounding Errors Are Not Random

This file records the exact Horner-form rational function, sampling grid,
continued-fraction reference, abstract `FPModel` rounded Horner operation
trace, and concrete IEEE-double finite round-to-even Horner trace from Higham
Section 1.17. It does not prove the visual nonrandom-error pattern in
Figure 1.6.
-/

/-- Kahan's Section 1.17 numerator in the displayed Horner form. -/
noncomputable def kahanHornerNumerator (x : ℝ) : ℝ :=
  622 - x * (751 - x * (324 - x * (59 - 4 * x)))

/-- Kahan's Section 1.17 denominator in the displayed Horner form. -/
noncomputable def kahanHornerDenominator (x : ℝ) : ℝ :=
  112 - x * (151 - x * (72 - x * (14 - x)))

/-- Kahan's Section 1.17 rational function. -/
noncomputable def kahanRationalFunction (x : ℝ) : ℝ :=
  kahanHornerNumerator x / kahanHornerDenominator x

/-! ## Continued-fraction reference curve -/

/-- The innermost nonconstant denominator in the continued-fraction
representation of Kahan's rational function. -/
noncomputable def kahanContinuedFractionTail1 (x : ℝ) : ℝ :=
  (x - 2) - 2 / (x - 3)

/-- The next denominator in the continued-fraction representation of Kahan's
rational function. -/
noncomputable def kahanContinuedFractionTail2 (x : ℝ) : ℝ :=
  (x - 7) + 10 / kahanContinuedFractionTail1 x

/-- The outer denominator in the continued-fraction representation of Kahan's
rational function. -/
noncomputable def kahanContinuedFractionTail3 (x : ℝ) : ℝ :=
  (x - 2) - 1 / kahanContinuedFractionTail2 x

/-- Continued-fraction representation used as the exact reference curve for
the §1.17 Kahan example. -/
noncomputable def kahanContinuedFraction (x : ℝ) : ℝ :=
  4 - 3 / kahanContinuedFractionTail3 x

/-- Quadratic denominator produced by the Euclidean derivation of the
continued fraction. -/
noncomputable def kahanContinuedFractionP2 (x : ℝ) : ℝ :=
  x ^ 2 - 5 * x + 4

/-- Cubic denominator produced by the Euclidean derivation of the continued
fraction. -/
noncomputable def kahanContinuedFractionP1 (x : ℝ) : ℝ :=
  x ^ 3 - 12 * x ^ 2 + 49 * x - 58

/-! ## Rounded Horner operation traces -/

/-- Rounded Horner evaluation of Kahan's numerator using the displayed
operation order. -/
noncomputable def flKahanHornerNumerator (fp : FPModel) (x : ℝ) : ℝ :=
  let m0 := fp.fl_mul 4 x
  let s0 := fp.fl_sub 59 m0
  let m1 := fp.fl_mul x s0
  let s1 := fp.fl_sub 324 m1
  let m2 := fp.fl_mul x s1
  let s2 := fp.fl_sub 751 m2
  let m3 := fp.fl_mul x s2
  fp.fl_sub 622 m3

/-- Rounded Horner evaluation of Kahan's denominator using the displayed
operation order. -/
noncomputable def flKahanHornerDenominator (fp : FPModel) (x : ℝ) : ℝ :=
  let s0 := fp.fl_sub 14 x
  let m1 := fp.fl_mul x s0
  let s1 := fp.fl_sub 72 m1
  let m2 := fp.fl_mul x s1
  let s2 := fp.fl_sub 151 m2
  let m3 := fp.fl_mul x s2
  fp.fl_sub 112 m3

/-- Rounded Horner quotient path: evaluate numerator and denominator by the
displayed Horner schemes and then perform one rounded division. -/
noncomputable def flKahanRationalFunction (fp : FPModel) (x : ℝ) : ℝ :=
  fp.fl_div (flKahanHornerNumerator fp x) (flKahanHornerDenominator fp x)

/-- Symbolic local-error expansion for the rounded numerator Horner trace. -/
noncomputable def kahanHornerNumeratorErrorEval (x : ℝ) (δ : Fin 8 → ℝ) : ℝ :=
  let m0 := (4 * x) * (1 + δ 0)
  let s0 := (59 - m0) * (1 + δ 1)
  let m1 := (x * s0) * (1 + δ 2)
  let s1 := (324 - m1) * (1 + δ 3)
  let m2 := (x * s1) * (1 + δ 4)
  let s2 := (751 - m2) * (1 + δ 5)
  let m3 := (x * s2) * (1 + δ 6)
  (622 - m3) * (1 + δ 7)

/-- Symbolic local-error expansion for the rounded denominator Horner trace. -/
noncomputable def kahanHornerDenominatorErrorEval (x : ℝ) (δ : Fin 7 → ℝ) : ℝ :=
  let s0 := (14 - x) * (1 + δ 0)
  let m1 := (x * s0) * (1 + δ 1)
  let s1 := (72 - m1) * (1 + δ 2)
  let m2 := (x * s1) * (1 + δ 3)
  let s2 := (151 - m2) * (1 + δ 4)
  let m3 := (x * s2) * (1 + δ 5)
  (112 - m3) * (1 + δ 6)

/-- The rounded numerator Horner trace has one bounded local relative-error
factor for each of its eight primitive operations. -/
theorem flKahanHornerNumerator_eq_errorEval (fp : FPModel) (x : ℝ) :
    ∃ δ : Fin 8 → ℝ,
      (∀ i, |δ i| ≤ fp.u) ∧
        flKahanHornerNumerator fp x =
          kahanHornerNumeratorErrorEval x δ := by
  rcases fp.model_mul 4 x with ⟨δ0, hδ0, hm0⟩
  let m0 := fp.fl_mul 4 x
  rcases fp.model_sub 59 m0 with ⟨δ1, hδ1, hs0⟩
  let s0 := fp.fl_sub 59 m0
  rcases fp.model_mul x s0 with ⟨δ2, hδ2, hm1⟩
  let m1 := fp.fl_mul x s0
  rcases fp.model_sub 324 m1 with ⟨δ3, hδ3, hs1⟩
  let s1 := fp.fl_sub 324 m1
  rcases fp.model_mul x s1 with ⟨δ4, hδ4, hm2⟩
  let m2 := fp.fl_mul x s1
  rcases fp.model_sub 751 m2 with ⟨δ5, hδ5, hs2⟩
  let s2 := fp.fl_sub 751 m2
  rcases fp.model_mul x s2 with ⟨δ6, hδ6, hm3⟩
  let m3 := fp.fl_mul x s2
  rcases fp.model_sub 622 m3 with ⟨δ7, hδ7, hs3⟩
  refine ⟨![δ0, δ1, δ2, δ3, δ4, δ5, δ6, δ7], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [hδ0, hδ1, hδ2, hδ3, hδ4, hδ5, hδ6, hδ7]
  · change fp.fl_sub 622 m3 =
        kahanHornerNumeratorErrorEval x ![δ0, δ1, δ2, δ3, δ4, δ5, δ6, δ7]
    rw [hs3]
    dsimp [kahanHornerNumeratorErrorEval]
    rw [show m3 = x * s2 * (1 + δ6) by simpa [m3] using hm3]
    rw [show s2 = (751 - m2) * (1 + δ5) by simpa [s2] using hs2]
    rw [show m2 = x * s1 * (1 + δ4) by simpa [m2] using hm2]
    rw [show s1 = (324 - m1) * (1 + δ3) by simpa [s1] using hs1]
    rw [show m1 = x * s0 * (1 + δ2) by simpa [m1] using hm1]
    rw [show s0 = (59 - m0) * (1 + δ1) by simpa [s0] using hs0]
    rw [show m0 = 4 * x * (1 + δ0) by simpa [m0] using hm0]

/-- The rounded denominator Horner trace has one bounded local relative-error
factor for each of its seven primitive operations. -/
theorem flKahanHornerDenominator_eq_errorEval (fp : FPModel) (x : ℝ) :
    ∃ δ : Fin 7 → ℝ,
      (∀ i, |δ i| ≤ fp.u) ∧
        flKahanHornerDenominator fp x =
          kahanHornerDenominatorErrorEval x δ := by
  rcases fp.model_sub 14 x with ⟨δ0, hδ0, hs0⟩
  let s0 := fp.fl_sub 14 x
  rcases fp.model_mul x s0 with ⟨δ1, hδ1, hm1⟩
  let m1 := fp.fl_mul x s0
  rcases fp.model_sub 72 m1 with ⟨δ2, hδ2, hs1⟩
  let s1 := fp.fl_sub 72 m1
  rcases fp.model_mul x s1 with ⟨δ3, hδ3, hm2⟩
  let m2 := fp.fl_mul x s1
  rcases fp.model_sub 151 m2 with ⟨δ4, hδ4, hs2⟩
  let s2 := fp.fl_sub 151 m2
  rcases fp.model_mul x s2 with ⟨δ5, hδ5, hm3⟩
  let m3 := fp.fl_mul x s2
  rcases fp.model_sub 112 m3 with ⟨δ6, hδ6, hs3⟩
  refine ⟨![δ0, δ1, δ2, δ3, δ4, δ5, δ6], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [hδ0, hδ1, hδ2, hδ3, hδ4, hδ5, hδ6]
  · change fp.fl_sub 112 m3 =
        kahanHornerDenominatorErrorEval x ![δ0, δ1, δ2, δ3, δ4, δ5, δ6]
    rw [hs3]
    dsimp [kahanHornerDenominatorErrorEval]
    rw [show m3 = x * s2 * (1 + δ5) by simpa [m3] using hm3]
    rw [show s2 = (151 - m2) * (1 + δ4) by simpa [s2] using hs2]
    rw [show m2 = x * s1 * (1 + δ3) by simpa [m2] using hm2]
    rw [show s1 = (72 - m1) * (1 + δ2) by simpa [s1] using hs1]
    rw [show m1 = x * s0 * (1 + δ1) by simpa [m1] using hm1]
    rw [show s0 = (14 - x) * (1 + δ0) by simpa [s0] using hs0]

/-- The rounded Kahan quotient path is the numerator and denominator Horner
local-error expansions followed by one rounded division. -/
theorem flKahanRationalFunction_eq_errorEval (fp : FPModel) (x : ℝ)
    (hden : flKahanHornerDenominator fp x ≠ 0) :
    ∃ δN : Fin 8 → ℝ, ∃ δD : Fin 7 → ℝ, ∃ δq : ℝ,
      (∀ i, |δN i| ≤ fp.u) ∧
      (∀ i, |δD i| ≤ fp.u) ∧
      |δq| ≤ fp.u ∧
        flKahanRationalFunction fp x =
          (kahanHornerNumeratorErrorEval x δN /
            kahanHornerDenominatorErrorEval x δD) * (1 + δq) := by
  rcases flKahanHornerNumerator_eq_errorEval fp x with ⟨δN, hδN, hnum⟩
  rcases flKahanHornerDenominator_eq_errorEval fp x with ⟨δD, hδD, hdenEval⟩
  rcases fp.model_div (flKahanHornerNumerator fp x)
      (flKahanHornerDenominator fp x) hden with ⟨δq, hδq, hdiv⟩
  refine ⟨δN, δD, δq, hδN, hδD, hδq, ?_⟩
  simp [flKahanRationalFunction, hnum, hdenEval] at hdiv ⊢
  exact hdiv

/-! ## IEEE-double finite round-to-even Horner trace -/

noncomputable section IeeeDoubleHorner

/-- IEEE-double unit roundoff used by the concrete finite round-to-even
§1.17 Horner trace. -/
noncomputable def kahanIeeeDoubleUnitRoundoff : ℝ :=
  FloatingPointFormat.unitRoundoff FloatingPointFormat.ieeeDoubleFormat

/-- First rounded numerator Horner intermediate, `fl(4*x)`, in IEEE double. -/
noncomputable def ieeeDoubleKahanNumerator_m0 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul 4 x

/-- Second rounded numerator Horner intermediate, `fl(59 - m0)`, in IEEE
double. -/
noncomputable def ieeeDoubleKahanNumerator_s0 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub 59
    (ieeeDoubleKahanNumerator_m0 x)

/-- Third rounded numerator Horner intermediate, `fl(x*s0)`, in IEEE double. -/
noncomputable def ieeeDoubleKahanNumerator_m1 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul x
    (ieeeDoubleKahanNumerator_s0 x)

/-- Fourth rounded numerator Horner intermediate, `fl(324 - m1)`, in IEEE
double. -/
noncomputable def ieeeDoubleKahanNumerator_s1 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub 324
    (ieeeDoubleKahanNumerator_m1 x)

/-- Fifth rounded numerator Horner intermediate, `fl(x*s1)`, in IEEE double. -/
noncomputable def ieeeDoubleKahanNumerator_m2 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul x
    (ieeeDoubleKahanNumerator_s1 x)

/-- Sixth rounded numerator Horner intermediate, `fl(751 - m2)`, in IEEE
double. -/
noncomputable def ieeeDoubleKahanNumerator_s2 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub 751
    (ieeeDoubleKahanNumerator_m2 x)

/-- Seventh rounded numerator Horner intermediate, `fl(x*s2)`, in IEEE
double. -/
noncomputable def ieeeDoubleKahanNumerator_m3 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul x
    (ieeeDoubleKahanNumerator_s2 x)

/-- IEEE-double finite round-to-even numerator Horner evaluation in the
displayed operation order. -/
noncomputable def ieeeDoubleKahanHornerNumerator (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub 622
    (ieeeDoubleKahanNumerator_m3 x)

/-- First rounded denominator Horner intermediate, `fl(14 - x)`, in IEEE
double. -/
noncomputable def ieeeDoubleKahanDenominator_s0 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub 14 x

/-- Second rounded denominator Horner intermediate, `fl(x*s0)`, in IEEE
double. -/
noncomputable def ieeeDoubleKahanDenominator_m1 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul x
    (ieeeDoubleKahanDenominator_s0 x)

/-- Third rounded denominator Horner intermediate, `fl(72 - m1)`, in IEEE
double. -/
noncomputable def ieeeDoubleKahanDenominator_s1 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub 72
    (ieeeDoubleKahanDenominator_m1 x)

/-- Fourth rounded denominator Horner intermediate, `fl(x*s1)`, in IEEE
double. -/
noncomputable def ieeeDoubleKahanDenominator_m2 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul x
    (ieeeDoubleKahanDenominator_s1 x)

/-- Fifth rounded denominator Horner intermediate, `fl(151 - m2)`, in IEEE
double. -/
noncomputable def ieeeDoubleKahanDenominator_s2 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub 151
    (ieeeDoubleKahanDenominator_m2 x)

/-- Sixth rounded denominator Horner intermediate, `fl(x*s2)`, in IEEE
double. -/
noncomputable def ieeeDoubleKahanDenominator_m3 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul x
    (ieeeDoubleKahanDenominator_s2 x)

/-- IEEE-double finite round-to-even denominator Horner evaluation in the
displayed operation order. -/
noncomputable def ieeeDoubleKahanHornerDenominator (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub 112
    (ieeeDoubleKahanDenominator_m3 x)

/-- IEEE-double finite round-to-even Horner quotient path. -/
noncomputable def ieeeDoubleKahanRationalFunction (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
    (ieeeDoubleKahanHornerNumerator x) (ieeeDoubleKahanHornerDenominator x)

/-- Normal-range obligations for the IEEE-double numerator Horner trace.
The fields are deliberately the exact primitive results in the actual rounded
operation order. -/
structure IeeeDoubleKahanNumeratorNormalTrace (x : ℝ) : Prop where
  m0 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.mul 4 x)
  s0 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.sub 59 (ieeeDoubleKahanNumerator_m0 x))
  m1 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanNumerator_s0 x))
  s1 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.sub 324 (ieeeDoubleKahanNumerator_m1 x))
  m2 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanNumerator_s1 x))
  s2 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.sub 751 (ieeeDoubleKahanNumerator_m2 x))
  m3 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanNumerator_s2 x))
  result : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.sub 622 (ieeeDoubleKahanNumerator_m3 x))

/-- Normal-range obligations for the IEEE-double denominator Horner trace. -/
structure IeeeDoubleKahanDenominatorNormalTrace (x : ℝ) : Prop where
  s0 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.sub 14 x)
  m1 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanDenominator_s0 x))
  s1 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.sub 72 (ieeeDoubleKahanDenominator_m1 x))
  m2 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanDenominator_s1 x))
  s2 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.sub 151 (ieeeDoubleKahanDenominator_m2 x))
  m3 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanDenominator_s2 x))
  result : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.sub 112 (ieeeDoubleKahanDenominator_m3 x))

/-- Normal-range obligations for the complete IEEE-double Horner quotient
trace. -/
structure IeeeDoubleKahanQuotientNormalTrace (x : ℝ) : Prop where
  numerator : IeeeDoubleKahanNumeratorNormalTrace x
  denominator : IeeeDoubleKahanDenominatorNormalTrace x
  quotient : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.div (ieeeDoubleKahanHornerNumerator x)
      (ieeeDoubleKahanHornerDenominator x))

/-- IEEE-double numerator Horner evaluation reduces to the same local-error
expansion as the abstract `FPModel` trace, with strict IEEE-double unit-roundoff
bounds, provided the actual primitive exact results stay in the finite normal
range. -/
theorem ieeeDoubleKahanHornerNumerator_eq_errorEval_of_finiteNormal
    (x : ℝ) (h : IeeeDoubleKahanNumeratorNormalTrace x) :
    ∃ δ : Fin 8 → ℝ,
      (∀ i, |δ i| < kahanIeeeDoubleUnitRoundoff) ∧
        ieeeDoubleKahanHornerNumerator x =
          kahanHornerNumeratorErrorEval x δ := by
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := 4) (y := x) h.m0 with ⟨δ0, hδ0, hm0⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 59) (y := ieeeDoubleKahanNumerator_m0 x) h.s0 with
    ⟨δ1, hδ1, hs0⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanNumerator_s0 x) h.m1 with
    ⟨δ2, hδ2, hm1⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 324) (y := ieeeDoubleKahanNumerator_m1 x) h.s1 with
    ⟨δ3, hδ3, hs1⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanNumerator_s1 x) h.m2 with
    ⟨δ4, hδ4, hm2⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 751) (y := ieeeDoubleKahanNumerator_m2 x) h.s2 with
    ⟨δ5, hδ5, hs2⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanNumerator_s2 x) h.m3 with
    ⟨δ6, hδ6, hm3⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 622) (y := ieeeDoubleKahanNumerator_m3 x) h.result with
    ⟨δ7, hδ7, hs3⟩
  refine ⟨![δ0, δ1, δ2, δ3, δ4, δ5, δ6, δ7], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [kahanIeeeDoubleUnitRoundoff, hδ0, hδ1, hδ2, hδ3,
      hδ4, hδ5, hδ6, hδ7]
  · change FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub
        622 (ieeeDoubleKahanNumerator_m3 x) =
        kahanHornerNumeratorErrorEval x ![δ0, δ1, δ2, δ3, δ4, δ5, δ6, δ7]
    rw [hs3]
    dsimp [kahanHornerNumeratorErrorEval]
    rw [show ieeeDoubleKahanNumerator_m3 x =
        x * ieeeDoubleKahanNumerator_s2 x * (1 + δ6) by
        simpa [ieeeDoubleKahanNumerator_m3, BasicOp.exact] using hm3]
    rw [show ieeeDoubleKahanNumerator_s2 x =
        (751 - ieeeDoubleKahanNumerator_m2 x) * (1 + δ5) by
        simpa [ieeeDoubleKahanNumerator_s2, BasicOp.exact] using hs2]
    rw [show ieeeDoubleKahanNumerator_m2 x =
        x * ieeeDoubleKahanNumerator_s1 x * (1 + δ4) by
        simpa [ieeeDoubleKahanNumerator_m2, BasicOp.exact] using hm2]
    rw [show ieeeDoubleKahanNumerator_s1 x =
        (324 - ieeeDoubleKahanNumerator_m1 x) * (1 + δ3) by
        simpa [ieeeDoubleKahanNumerator_s1, BasicOp.exact] using hs1]
    rw [show ieeeDoubleKahanNumerator_m1 x =
        x * ieeeDoubleKahanNumerator_s0 x * (1 + δ2) by
        simpa [ieeeDoubleKahanNumerator_m1, BasicOp.exact] using hm1]
    rw [show ieeeDoubleKahanNumerator_s0 x =
        (59 - ieeeDoubleKahanNumerator_m0 x) * (1 + δ1) by
        simpa [ieeeDoubleKahanNumerator_s0, BasicOp.exact] using hs0]
    rw [show ieeeDoubleKahanNumerator_m0 x =
        4 * x * (1 + δ0) by
        simpa [ieeeDoubleKahanNumerator_m0, BasicOp.exact] using hm0]
    simp [BasicOp.exact]

/-- IEEE-double denominator Horner evaluation reduces to the same local-error
expansion as the abstract trace under the corresponding finite-normal
obligations. -/
theorem ieeeDoubleKahanHornerDenominator_eq_errorEval_of_finiteNormal
    (x : ℝ) (h : IeeeDoubleKahanDenominatorNormalTrace x) :
    ∃ δ : Fin 7 → ℝ,
      (∀ i, |δ i| < kahanIeeeDoubleUnitRoundoff) ∧
        ieeeDoubleKahanHornerDenominator x =
          kahanHornerDenominatorErrorEval x δ := by
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 14) (y := x) h.s0 with ⟨δ0, hδ0, hs0⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanDenominator_s0 x) h.m1 with
    ⟨δ1, hδ1, hm1⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 72) (y := ieeeDoubleKahanDenominator_m1 x) h.s1 with
    ⟨δ2, hδ2, hs1⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanDenominator_s1 x) h.m2 with
    ⟨δ3, hδ3, hm2⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 151) (y := ieeeDoubleKahanDenominator_m2 x) h.s2 with
    ⟨δ4, hδ4, hs2⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanDenominator_s2 x) h.m3 with
    ⟨δ5, hδ5, hm3⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 112) (y := ieeeDoubleKahanDenominator_m3 x) h.result with
    ⟨δ6, hδ6, hs3⟩
  refine ⟨![δ0, δ1, δ2, δ3, δ4, δ5, δ6], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [kahanIeeeDoubleUnitRoundoff, hδ0, hδ1, hδ2, hδ3,
      hδ4, hδ5, hδ6]
  · change FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub
        112 (ieeeDoubleKahanDenominator_m3 x) =
        kahanHornerDenominatorErrorEval x ![δ0, δ1, δ2, δ3, δ4, δ5, δ6]
    rw [hs3]
    dsimp [kahanHornerDenominatorErrorEval]
    rw [show ieeeDoubleKahanDenominator_m3 x =
        x * ieeeDoubleKahanDenominator_s2 x * (1 + δ5) by
        simpa [ieeeDoubleKahanDenominator_m3, BasicOp.exact] using hm3]
    rw [show ieeeDoubleKahanDenominator_s2 x =
        (151 - ieeeDoubleKahanDenominator_m2 x) * (1 + δ4) by
        simpa [ieeeDoubleKahanDenominator_s2, BasicOp.exact] using hs2]
    rw [show ieeeDoubleKahanDenominator_m2 x =
        x * ieeeDoubleKahanDenominator_s1 x * (1 + δ3) by
        simpa [ieeeDoubleKahanDenominator_m2, BasicOp.exact] using hm2]
    rw [show ieeeDoubleKahanDenominator_s1 x =
        (72 - ieeeDoubleKahanDenominator_m1 x) * (1 + δ2) by
        simpa [ieeeDoubleKahanDenominator_s1, BasicOp.exact] using hs1]
    rw [show ieeeDoubleKahanDenominator_m1 x =
        x * ieeeDoubleKahanDenominator_s0 x * (1 + δ1) by
        simpa [ieeeDoubleKahanDenominator_m1, BasicOp.exact] using hm1]
    rw [show ieeeDoubleKahanDenominator_s0 x =
        (14 - x) * (1 + δ0) by
        simpa [ieeeDoubleKahanDenominator_s0, BasicOp.exact] using hs0]
    simp [BasicOp.exact]

/-- Complete IEEE-double finite round-to-even Horner quotient trace, reduced
to the numerator/denominator local-error expansions plus the final division
factor.  This is the concrete double-precision operation-order bridge; it does
not prove the Figure 1.6 rounded-value pattern. -/
theorem ieeeDoubleKahanRationalFunction_eq_errorEval_of_finiteNormal
    (x : ℝ) (h : IeeeDoubleKahanQuotientNormalTrace x) :
    ∃ δN : Fin 8 → ℝ, ∃ δD : Fin 7 → ℝ, ∃ δq : ℝ,
      (∀ i, |δN i| < kahanIeeeDoubleUnitRoundoff) ∧
      (∀ i, |δD i| < kahanIeeeDoubleUnitRoundoff) ∧
      |δq| < kahanIeeeDoubleUnitRoundoff ∧
        ieeeDoubleKahanRationalFunction x =
          (kahanHornerNumeratorErrorEval x δN /
            kahanHornerDenominatorErrorEval x δD) * (1 + δq) := by
  rcases ieeeDoubleKahanHornerNumerator_eq_errorEval_of_finiteNormal x
      h.numerator with ⟨δN, hδN, hnum⟩
  rcases ieeeDoubleKahanHornerDenominator_eq_errorEval_of_finiteNormal x
      h.denominator with ⟨δD, hδD, hden⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.div)
      (x := ieeeDoubleKahanHornerNumerator x)
      (y := ieeeDoubleKahanHornerDenominator x) h.quotient with
    ⟨δq, hδq, hquot⟩
  refine ⟨δN, δD, δq, hδN, hδD, ?_, ?_⟩
  · simpa [kahanIeeeDoubleUnitRoundoff] using hδq
  · simp [ieeeDoubleKahanRationalFunction, BasicOp.exact, hnum, hden] at hquot ⊢
    exact hquot

end IeeeDoubleHorner

/-! ## IEEE-double source-grid normal-range certificates -/

private theorem kahanIeeeDoubleUnitRoundoff_lt_one_thousandth :
    kahanIeeeDoubleUnitRoundoff < (1 : ℝ) / 1000 := by
  rw [kahanIeeeDoubleUnitRoundoff,
    FloatingPointFormat.ieeeDoubleFormat_unitRoundoff]
  norm_num [zpow_neg]

private theorem kahanIeeeDouble_delta_bounds
    {δ : ℝ} (hδ : |δ| < kahanIeeeDoubleUnitRoundoff) :
    (999 : ℝ) / 1000 < 1 + δ ∧
      1 + δ < (1001 : ℝ) / 1000 := by
  have hδu := abs_lt.mp hδ
  have hu := kahanIeeeDoubleUnitRoundoff_lt_one_thousandth
  constructor <;> nlinarith

private theorem ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    {z : ℝ} (hzlo : (1 : ℝ) ≤ |z|) (hzhi : |z| ≤ 1000) :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange z := by
  constructor
  · have hmin : FloatingPointFormat.ieeeDoubleFormat.minNormalMagnitude ≤
        (1 : ℝ) := by
      norm_num [FloatingPointFormat.minNormalMagnitude,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
      exact inv_le_one_of_one_le₀
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    exact le_trans hmin hzlo
  · have hmax : (1000 : ℝ) ≤
        FloatingPointFormat.ieeeDoubleFormat.maxFiniteMagnitude := by
      norm_num [FloatingPointFormat.maxFiniteMagnitude,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
      have hpow : (2000 : ℝ) ≤ 2 ^ 1024 := by
        have h11 : (2000 : ℝ) ≤ 2 ^ 11 := by norm_num
        have hmono : (2 : ℝ) ^ 11 ≤ 2 ^ 1024 :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num)
        exact le_trans h11 hmono
      have hfrac :
          (1 : ℝ) / 2 ≤
            (9007199254740991 : ℝ) / 9007199254740992 := by
        norm_num
      have hprod :
          (2000 : ℝ) * ((1 : ℝ) / 2) ≤
            2 ^ 1024 *
              ((9007199254740991 : ℝ) / 9007199254740992) :=
        mul_le_mul hpow hfrac (by norm_num) (by positivity)
      norm_num at hprod
      exact hprod
    exact le_trans hzhi hmax

private theorem ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    {z : ℝ} (hzlo : (1 : ℝ) ≤ z) (hzhi : z ≤ 1000) :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange z := by
  apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
  · rwa [abs_of_nonneg (le_trans zero_le_one hzlo)]
  · rwa [abs_of_nonneg (le_trans zero_le_one hzlo)]

private theorem mul_interval_mono
    {a b la ua lb ub : ℝ} (hla : la ≤ a) (hua : a ≤ ua)
    (hlb : lb ≤ b) (hub : b ≤ ub) (hla0 : 0 ≤ la) (hlb0 : 0 ≤ lb) :
    la * lb ≤ a * b ∧ a * b ≤ ua * ub := by
  constructor
  · exact mul_le_mul hla hlb hlb0 (le_trans hla0 hla)
  · exact mul_le_mul hua hub (le_trans hlb0 hlb)
      (le_trans hla0 (le_trans hla hua))

private theorem kahan_source_interval_x_bounds
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    (803 : ℝ) / 500 ≤ x ∧ x ≤ (1607 : ℝ) / 1000 := by
  refine ⟨hxlo, ?_⟩
  have htail :
      (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52 ≤
        (1607 : ℝ) / 1000 := by
    norm_num
  exact le_trans hxhi htail

private theorem kahan_source_interval_ieeeDouble_finiteNormalRange
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange x := by
  have hxb := kahan_source_interval_x_bounds hxlo hxhi
  apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
  · nlinarith
  · nlinarith

private theorem kahan_source_interval_numerator_m0_normal
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.mul 4 x) := by
  have hxb := kahan_source_interval_x_bounds hxlo hxhi
  apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
  · simp [BasicOp.exact]
    nlinarith
  · simp [BasicOp.exact]
    nlinarith

private theorem kahan_source_interval_denominator_s0_normal
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.sub 14 x) := by
  have hxb := kahan_source_interval_x_bounds hxlo hxhi
  apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
  · simp [BasicOp.exact]
    nlinarith
  · simp [BasicOp.exact]
    nlinarith

set_option maxHeartbeats 800000 in
theorem ieeeDoubleKahanNumeratorNormalTrace_of_source_interval
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    IeeeDoubleKahanNumeratorNormalTrace x := by
  have hxb := kahan_source_interval_x_bounds hxlo hxhi
  have hm0N := kahan_source_interval_numerator_m0_normal hxlo hxhi
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := 4) (y := x) hm0N with ⟨δm0, hδm0, hm0eq⟩
  have hδm0b := kahanIeeeDouble_delta_bounds hδm0
  have hm0eq' :
      ieeeDoubleKahanNumerator_m0 x = (4 * x) * (1 + δm0) := by
    simpa [ieeeDoubleKahanNumerator_m0, BasicOp.exact] using hm0eq
  have hm0_exact_lo : (6 : ℝ) ≤ 4 * x := by linarith [hxb.1]
  have hm0_exact_hi : 4 * x ≤ 7 := by linarith [hxb.2]
  have hm0_prod :=
    mul_interval_mono hm0_exact_lo hm0_exact_hi
      (le_of_lt hδm0b.1) (le_of_lt hδm0b.2)
      (by norm_num : (0 : ℝ) ≤ 6)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm0_lo : (5 : ℝ) ≤ ieeeDoubleKahanNumerator_m0 x := by
    rw [hm0eq']
    linarith [hm0_prod.1]
  have hm0_hi : ieeeDoubleKahanNumerator_m0 x ≤ (8 : ℝ) := by
    rw [hm0eq']
    linarith [hm0_prod.2]
  have hs0N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.sub 59 (ieeeDoubleKahanNumerator_m0 x)) := by
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm0_hi]
    · simp [BasicOp.exact]
      linarith [hm0_lo]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 59) (y := ieeeDoubleKahanNumerator_m0 x) hs0N with
    ⟨δs0, hδs0, hs0eq⟩
  have hδs0b := kahanIeeeDouble_delta_bounds hδs0
  have hs0eq' :
      ieeeDoubleKahanNumerator_s0 x =
        (59 - ieeeDoubleKahanNumerator_m0 x) * (1 + δs0) := by
    simpa [ieeeDoubleKahanNumerator_s0, BasicOp.exact] using hs0eq
  have hs0_exact_lo : (51 : ℝ) ≤ 59 - ieeeDoubleKahanNumerator_m0 x := by
    linarith [hm0_hi]
  have hs0_exact_hi : 59 - ieeeDoubleKahanNumerator_m0 x ≤ (54 : ℝ) := by
    linarith [hm0_lo]
  have hs0_prod :=
    mul_interval_mono hs0_exact_lo hs0_exact_hi
      (le_of_lt hδs0b.1) (le_of_lt hδs0b.2)
      (by norm_num : (0 : ℝ) ≤ 51)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs0_lo : (50 : ℝ) ≤ ieeeDoubleKahanNumerator_s0 x := by
    rw [hs0eq']
    linarith [hs0_prod.1]
  have hs0_hi : ieeeDoubleKahanNumerator_s0 x ≤ (55 : ℝ) := by
    rw [hs0eq']
    linarith [hs0_prod.2]
  have hm1N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanNumerator_s0 x)) := by
    have hm1_prod :=
      mul_interval_mono hxb.1 hxb.2 hs0_lo hs0_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ 50)
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm1_prod.1]
    · simp [BasicOp.exact]
      linarith [hm1_prod.2]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanNumerator_s0 x) hm1N with
    ⟨δm1, hδm1, hm1eq⟩
  have hδm1b := kahanIeeeDouble_delta_bounds hδm1
  have hm1eq' :
      ieeeDoubleKahanNumerator_m1 x =
        (x * ieeeDoubleKahanNumerator_s0 x) * (1 + δm1) := by
    simpa [ieeeDoubleKahanNumerator_m1, BasicOp.exact] using hm1eq
  have hm1_exact_lo : (80 : ℝ) ≤ x * ieeeDoubleKahanNumerator_s0 x := by
    have hm1_prod :=
      mul_interval_mono hxb.1 hxb.2 hs0_lo hs0_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ 50)
    linarith [hm1_prod.1]
  have hm1_exact_hi : x * ieeeDoubleKahanNumerator_s0 x ≤ (89 : ℝ) := by
    have hm1_prod :=
      mul_interval_mono hxb.1 hxb.2 hs0_lo hs0_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ 50)
    linarith [hm1_prod.2]
  have hm1_prod_round :=
    mul_interval_mono hm1_exact_lo hm1_exact_hi
      (le_of_lt hδm1b.1) (le_of_lt hδm1b.2)
      (by norm_num : (0 : ℝ) ≤ 80)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm1_lo : (79 : ℝ) ≤ ieeeDoubleKahanNumerator_m1 x := by
    rw [hm1eq']
    linarith [hm1_prod_round.1]
  have hm1_hi : ieeeDoubleKahanNumerator_m1 x ≤ (90 : ℝ) := by
    rw [hm1eq']
    linarith [hm1_prod_round.2]
  have hs1N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.sub 324 (ieeeDoubleKahanNumerator_m1 x)) := by
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm1_hi]
    · simp [BasicOp.exact]
      linarith [hm1_lo]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 324) (y := ieeeDoubleKahanNumerator_m1 x) hs1N with
    ⟨δs1, hδs1, hs1eq⟩
  have hδs1b := kahanIeeeDouble_delta_bounds hδs1
  have hs1eq' :
      ieeeDoubleKahanNumerator_s1 x =
        (324 - ieeeDoubleKahanNumerator_m1 x) * (1 + δs1) := by
    simpa [ieeeDoubleKahanNumerator_s1, BasicOp.exact] using hs1eq
  have hs1_exact_lo : (234 : ℝ) ≤ 324 - ieeeDoubleKahanNumerator_m1 x := by
    linarith [hm1_hi]
  have hs1_exact_hi : 324 - ieeeDoubleKahanNumerator_m1 x ≤ (245 : ℝ) := by
    linarith [hm1_lo]
  have hs1_prod_round :=
    mul_interval_mono hs1_exact_lo hs1_exact_hi
      (le_of_lt hδs1b.1) (le_of_lt hδs1b.2)
      (by norm_num : (0 : ℝ) ≤ 234)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs1_lo : (233 : ℝ) ≤ ieeeDoubleKahanNumerator_s1 x := by
    rw [hs1eq']
    linarith [hs1_prod_round.1]
  have hs1_hi : ieeeDoubleKahanNumerator_s1 x ≤ (246 : ℝ) := by
    rw [hs1eq']
    linarith [hs1_prod_round.2]
  have hm2N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanNumerator_s1 x)) := by
    have hm2_prod :=
      mul_interval_mono hxb.1 hxb.2 hs1_lo hs1_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ 233)
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm2_prod.1]
    · simp [BasicOp.exact]
      linarith [hm2_prod.2]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanNumerator_s1 x) hm2N with
    ⟨δm2, hδm2, hm2eq⟩
  have hδm2b := kahanIeeeDouble_delta_bounds hδm2
  have hm2eq' :
      ieeeDoubleKahanNumerator_m2 x =
        (x * ieeeDoubleKahanNumerator_s1 x) * (1 + δm2) := by
    simpa [ieeeDoubleKahanNumerator_m2, BasicOp.exact] using hm2eq
  have hm2_exact_lo : (374 : ℝ) ≤ x * ieeeDoubleKahanNumerator_s1 x := by
    have hm2_prod :=
      mul_interval_mono hxb.1 hxb.2 hs1_lo hs1_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ 233)
    linarith [hm2_prod.1]
  have hm2_exact_hi : x * ieeeDoubleKahanNumerator_s1 x ≤ (396 : ℝ) := by
    have hm2_prod :=
      mul_interval_mono hxb.1 hxb.2 hs1_lo hs1_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ 233)
    linarith [hm2_prod.2]
  have hm2_prod_round :=
    mul_interval_mono hm2_exact_lo hm2_exact_hi
      (le_of_lt hδm2b.1) (le_of_lt hδm2b.2)
      (by norm_num : (0 : ℝ) ≤ 374)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm2_lo : (373 : ℝ) ≤ ieeeDoubleKahanNumerator_m2 x := by
    rw [hm2eq']
    linarith [hm2_prod_round.1]
  have hm2_hi : ieeeDoubleKahanNumerator_m2 x ≤ (397 : ℝ) := by
    rw [hm2eq']
    linarith [hm2_prod_round.2]
  have hs2N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.sub 751 (ieeeDoubleKahanNumerator_m2 x)) := by
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm2_hi]
    · simp [BasicOp.exact]
      linarith [hm2_lo]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 751) (y := ieeeDoubleKahanNumerator_m2 x) hs2N with
    ⟨δs2, hδs2, hs2eq⟩
  have hδs2b := kahanIeeeDouble_delta_bounds hδs2
  have hs2eq' :
      ieeeDoubleKahanNumerator_s2 x =
        (751 - ieeeDoubleKahanNumerator_m2 x) * (1 + δs2) := by
    simpa [ieeeDoubleKahanNumerator_s2, BasicOp.exact] using hs2eq
  have hs2_exact_lo : (354 : ℝ) ≤ 751 - ieeeDoubleKahanNumerator_m2 x := by
    linarith [hm2_hi]
  have hs2_exact_hi : 751 - ieeeDoubleKahanNumerator_m2 x ≤ (378 : ℝ) := by
    linarith [hm2_lo]
  have hs2_prod_round :=
    mul_interval_mono hs2_exact_lo hs2_exact_hi
      (le_of_lt hδs2b.1) (le_of_lt hδs2b.2)
      (by norm_num : (0 : ℝ) ≤ 354)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs2_lo : (353 : ℝ) ≤ ieeeDoubleKahanNumerator_s2 x := by
    rw [hs2eq']
    linarith [hs2_prod_round.1]
  have hs2_hi : ieeeDoubleKahanNumerator_s2 x ≤ (379 : ℝ) := by
    rw [hs2eq']
    linarith [hs2_prod_round.2]
  have hm3N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanNumerator_s2 x)) := by
    have hm3_prod :=
      mul_interval_mono hxb.1 hxb.2 hs2_lo hs2_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ 353)
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm3_prod.1]
    · simp [BasicOp.exact]
      linarith [hm3_prod.2]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanNumerator_s2 x) hm3N with
    ⟨δm3, hδm3, hm3eq⟩
  have hδm3b := kahanIeeeDouble_delta_bounds hδm3
  have hm3eq' :
      ieeeDoubleKahanNumerator_m3 x =
        (x * ieeeDoubleKahanNumerator_s2 x) * (1 + δm3) := by
    simpa [ieeeDoubleKahanNumerator_m3, BasicOp.exact] using hm3eq
  have hm3_exact_lo : (566 : ℝ) ≤ x * ieeeDoubleKahanNumerator_s2 x := by
    have hm3_prod :=
      mul_interval_mono hxb.1 hxb.2 hs2_lo hs2_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ 353)
    linarith [hm3_prod.1]
  have hm3_exact_hi : x * ieeeDoubleKahanNumerator_s2 x ≤ (610 : ℝ) := by
    have hm3_prod :=
      mul_interval_mono hxb.1 hxb.2 hs2_lo hs2_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ 353)
    linarith [hm3_prod.2]
  have hm3_prod_round :=
    mul_interval_mono hm3_exact_lo hm3_exact_hi
      (le_of_lt hδm3b.1) (le_of_lt hδm3b.2)
      (by norm_num : (0 : ℝ) ≤ 566)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm3_lo : (565 : ℝ) ≤ ieeeDoubleKahanNumerator_m3 x := by
    rw [hm3eq']
    linarith [hm3_prod_round.1]
  have hm3_hi : ieeeDoubleKahanNumerator_m3 x ≤ (611 : ℝ) := by
    rw [hm3eq']
    linarith [hm3_prod_round.2]
  have hresultN : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.sub 622 (ieeeDoubleKahanNumerator_m3 x)) := by
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm3_hi]
    · simp [BasicOp.exact]
      linarith [hm3_lo]
  exact
    { m0 := hm0N
      s0 := hs0N
      m1 := hm1N
      s1 := hs1N
      m2 := hm2N
      s2 := hs2N
      m3 := hm3N
      result := hresultN }

set_option maxHeartbeats 800000 in
theorem ieeeDoubleKahanDenominatorNormalTrace_of_source_interval
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    IeeeDoubleKahanDenominatorNormalTrace x := by
  have hxb := kahan_source_interval_x_bounds hxlo hxhi
  have hs0N := kahan_source_interval_denominator_s0_normal hxlo hxhi
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 14) (y := x) hs0N with ⟨δs0, hδs0, hs0eq⟩
  have hδs0b := kahanIeeeDouble_delta_bounds hδs0
  have hs0eq' :
      ieeeDoubleKahanDenominator_s0 x = (14 - x) * (1 + δs0) := by
    simpa [ieeeDoubleKahanDenominator_s0, BasicOp.exact] using hs0eq
  have hs0_exact_lo : (1239 : ℝ) / 100 ≤ 14 - x := by linarith [hxb.2]
  have hs0_exact_hi : 14 - x ≤ (25 : ℝ) / 2 := by linarith [hxb.1]
  have hs0_prod_round :=
    mul_interval_mono hs0_exact_lo hs0_exact_hi
      (le_of_lt hδs0b.1) (le_of_lt hδs0b.2)
      (by norm_num : (0 : ℝ) ≤ (1239 : ℝ) / 100)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs0_lo : (123 : ℝ) / 10 ≤ ieeeDoubleKahanDenominator_s0 x := by
    rw [hs0eq']
    linarith [hs0_prod_round.1]
  have hs0_hi : ieeeDoubleKahanDenominator_s0 x ≤ (63 : ℝ) / 5 := by
    rw [hs0eq']
    linarith [hs0_prod_round.2]
  have hm1N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanDenominator_s0 x)) := by
    have hm1_prod :=
      mul_interval_mono hxb.1 hxb.2 hs0_lo hs0_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ (123 : ℝ) / 10)
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm1_prod.1]
    · simp [BasicOp.exact]
      linarith [hm1_prod.2]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanDenominator_s0 x) hm1N with
    ⟨δm1, hδm1, hm1eq⟩
  have hδm1b := kahanIeeeDouble_delta_bounds hδm1
  have hm1eq' :
      ieeeDoubleKahanDenominator_m1 x =
        (x * ieeeDoubleKahanDenominator_s0 x) * (1 + δm1) := by
    simpa [ieeeDoubleKahanDenominator_m1, BasicOp.exact] using hm1eq
  have hm1_exact_lo : (197 : ℝ) / 10 ≤ x * ieeeDoubleKahanDenominator_s0 x := by
    have hm1_prod :=
      mul_interval_mono hxb.1 hxb.2 hs0_lo hs0_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ (123 : ℝ) / 10)
    linarith [hm1_prod.1]
  have hm1_exact_hi : x * ieeeDoubleKahanDenominator_s0 x ≤ (102 : ℝ) / 5 := by
    have hm1_prod :=
      mul_interval_mono hxb.1 hxb.2 hs0_lo hs0_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ (123 : ℝ) / 10)
    linarith [hm1_prod.2]
  have hm1_prod_round :=
    mul_interval_mono hm1_exact_lo hm1_exact_hi
      (le_of_lt hδm1b.1) (le_of_lt hδm1b.2)
      (by norm_num : (0 : ℝ) ≤ (197 : ℝ) / 10)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm1_lo : (98 : ℝ) / 5 ≤ ieeeDoubleKahanDenominator_m1 x := by
    rw [hm1eq']
    linarith [hm1_prod_round.1]
  have hm1_hi : ieeeDoubleKahanDenominator_m1 x ≤ (103 : ℝ) / 5 := by
    rw [hm1eq']
    linarith [hm1_prod_round.2]
  have hs1N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.sub 72 (ieeeDoubleKahanDenominator_m1 x)) := by
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm1_hi]
    · simp [BasicOp.exact]
      linarith [hm1_lo]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 72) (y := ieeeDoubleKahanDenominator_m1 x) hs1N with
    ⟨δs1, hδs1, hs1eq⟩
  have hδs1b := kahanIeeeDouble_delta_bounds hδs1
  have hs1eq' :
      ieeeDoubleKahanDenominator_s1 x =
        (72 - ieeeDoubleKahanDenominator_m1 x) * (1 + δs1) := by
    simpa [ieeeDoubleKahanDenominator_s1, BasicOp.exact] using hs1eq
  have hs1_exact_lo : (257 : ℝ) / 5 ≤ 72 - ieeeDoubleKahanDenominator_m1 x := by
    linarith [hm1_hi]
  have hs1_exact_hi : 72 - ieeeDoubleKahanDenominator_m1 x ≤ (262 : ℝ) / 5 := by
    linarith [hm1_lo]
  have hs1_prod_round :=
    mul_interval_mono hs1_exact_lo hs1_exact_hi
      (le_of_lt hδs1b.1) (le_of_lt hδs1b.2)
      (by norm_num : (0 : ℝ) ≤ (257 : ℝ) / 5)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs1_lo : (513 : ℝ) / 10 ≤ ieeeDoubleKahanDenominator_s1 x := by
    rw [hs1eq']
    linarith [hs1_prod_round.1]
  have hs1_hi : ieeeDoubleKahanDenominator_s1 x ≤ (105 : ℝ) / 2 := by
    rw [hs1eq']
    linarith [hs1_prod_round.2]
  have hm2N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanDenominator_s1 x)) := by
    have hm2_prod :=
      mul_interval_mono hxb.1 hxb.2 hs1_lo hs1_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ (513 : ℝ) / 10)
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm2_prod.1]
    · simp [BasicOp.exact]
      linarith [hm2_prod.2]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanDenominator_s1 x) hm2N with
    ⟨δm2, hδm2, hm2eq⟩
  have hδm2b := kahanIeeeDouble_delta_bounds hδm2
  have hm2eq' :
      ieeeDoubleKahanDenominator_m2 x =
        (x * ieeeDoubleKahanDenominator_s1 x) * (1 + δm2) := by
    simpa [ieeeDoubleKahanDenominator_m2, BasicOp.exact] using hm2eq
  have hm2_exact_lo : (823 : ℝ) / 10 ≤ x * ieeeDoubleKahanDenominator_s1 x := by
    have hm2_prod :=
      mul_interval_mono hxb.1 hxb.2 hs1_lo hs1_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ (513 : ℝ) / 10)
    linarith [hm2_prod.1]
  have hm2_exact_hi : x * ieeeDoubleKahanDenominator_s1 x ≤ (422 : ℝ) / 5 := by
    have hm2_prod :=
      mul_interval_mono hxb.1 hxb.2 hs1_lo hs1_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ (513 : ℝ) / 10)
    linarith [hm2_prod.2]
  have hm2_prod_round :=
    mul_interval_mono hm2_exact_lo hm2_exact_hi
      (le_of_lt hδm2b.1) (le_of_lt hδm2b.2)
      (by norm_num : (0 : ℝ) ≤ (823 : ℝ) / 10)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm2_lo : (411 : ℝ) / 5 ≤ ieeeDoubleKahanDenominator_m2 x := by
    rw [hm2eq']
    linarith [hm2_prod_round.1]
  have hm2_hi : ieeeDoubleKahanDenominator_m2 x ≤ (169 : ℝ) / 2 := by
    rw [hm2eq']
    linarith [hm2_prod_round.2]
  have hs2N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.sub 151 (ieeeDoubleKahanDenominator_m2 x)) := by
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm2_hi]
    · simp [BasicOp.exact]
      linarith [hm2_lo]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 151) (y := ieeeDoubleKahanDenominator_m2 x) hs2N with
    ⟨δs2, hδs2, hs2eq⟩
  have hδs2b := kahanIeeeDouble_delta_bounds hδs2
  have hs2eq' :
      ieeeDoubleKahanDenominator_s2 x =
        (151 - ieeeDoubleKahanDenominator_m2 x) * (1 + δs2) := by
    simpa [ieeeDoubleKahanDenominator_s2, BasicOp.exact] using hs2eq
  have hs2_exact_lo : (133 : ℝ) / 2 ≤ 151 - ieeeDoubleKahanDenominator_m2 x := by
    linarith [hm2_hi]
  have hs2_exact_hi : 151 - ieeeDoubleKahanDenominator_m2 x ≤ (344 : ℝ) / 5 := by
    linarith [hm2_lo]
  have hs2_prod_round :=
    mul_interval_mono hs2_exact_lo hs2_exact_hi
      (le_of_lt hδs2b.1) (le_of_lt hδs2b.2)
      (by norm_num : (0 : ℝ) ≤ (133 : ℝ) / 2)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs2_lo : (332 : ℝ) / 5 ≤ ieeeDoubleKahanDenominator_s2 x := by
    rw [hs2eq']
    linarith [hs2_prod_round.1]
  have hs2_hi : ieeeDoubleKahanDenominator_s2 x ≤ (689 : ℝ) / 10 := by
    rw [hs2eq']
    linarith [hs2_prod_round.2]
  have hm3N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanDenominator_s2 x)) := by
    have hm3_prod :=
      mul_interval_mono hxb.1 hxb.2 hs2_lo hs2_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ (332 : ℝ) / 5)
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm3_prod.1]
    · simp [BasicOp.exact]
      linarith [hm3_prod.2]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanDenominator_s2 x) hm3N with
    ⟨δm3, hδm3, hm3eq⟩
  have hδm3b := kahanIeeeDouble_delta_bounds hδm3
  have hm3eq' :
      ieeeDoubleKahanDenominator_m3 x =
        (x * ieeeDoubleKahanDenominator_s2 x) * (1 + δm3) := by
    simpa [ieeeDoubleKahanDenominator_m3, BasicOp.exact] using hm3eq
  have hm3_exact_lo : (106 : ℝ) ≤ x * ieeeDoubleKahanDenominator_s2 x := by
    have hm3_prod :=
      mul_interval_mono hxb.1 hxb.2 hs2_lo hs2_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ (332 : ℝ) / 5)
    linarith [hm3_prod.1]
  have hm3_exact_hi : x * ieeeDoubleKahanDenominator_s2 x ≤ (554 : ℝ) / 5 := by
    have hm3_prod :=
      mul_interval_mono hxb.1 hxb.2 hs2_lo hs2_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ (332 : ℝ) / 5)
    linarith [hm3_prod.2]
  have hm3_prod_round :=
    mul_interval_mono hm3_exact_lo hm3_exact_hi
      (le_of_lt hδm3b.1) (le_of_lt hδm3b.2)
      (by norm_num : (0 : ℝ) ≤ 106)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm3_lo : (105 : ℝ) ≤ ieeeDoubleKahanDenominator_m3 x := by
    rw [hm3eq']
    linarith [hm3_prod_round.1]
  have hm3_hi : ieeeDoubleKahanDenominator_m3 x ≤ (111 : ℝ) := by
    rw [hm3eq']
    linarith [hm3_prod_round.2]
  have hresultN : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.sub 112 (ieeeDoubleKahanDenominator_m3 x)) := by
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm3_hi]
    · simp [BasicOp.exact]
      linarith [hm3_lo]
  exact
    { s0 := hs0N
      m1 := hm1N
      s1 := hs1N
      m2 := hm2N
      s2 := hs2N
      m3 := hm3N
      result := hresultN }

set_option maxHeartbeats 800000 in
theorem kahanHornerNumeratorErrorEval_source_interval_bounds
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52)
    (δ : Fin 8 → ℝ) (hδ : ∀ i, |δ i| < kahanIeeeDoubleUnitRoundoff) :
    (10 : ℝ) ≤ kahanHornerNumeratorErrorEval x δ ∧
      kahanHornerNumeratorErrorEval x δ ≤ 58 := by
  have hxb := kahan_source_interval_x_bounds hxlo hxhi
  have hδ0 := kahanIeeeDouble_delta_bounds (hδ 0)
  have hδ1 := kahanIeeeDouble_delta_bounds (hδ 1)
  have hδ2 := kahanIeeeDouble_delta_bounds (hδ 2)
  have hδ3 := kahanIeeeDouble_delta_bounds (hδ 3)
  have hδ4 := kahanIeeeDouble_delta_bounds (hδ 4)
  have hδ5 := kahanIeeeDouble_delta_bounds (hδ 5)
  have hδ6 := kahanIeeeDouble_delta_bounds (hδ 6)
  have hδ7 := kahanIeeeDouble_delta_bounds (hδ 7)
  let m0 := (4 * x) * (1 + δ 0)
  have hm0_exact_lo : (6 : ℝ) ≤ 4 * x := by linarith [hxb.1]
  have hm0_exact_hi : 4 * x ≤ 7 := by linarith [hxb.2]
  have hm0_prod :=
    mul_interval_mono hm0_exact_lo hm0_exact_hi
      (le_of_lt hδ0.1) (le_of_lt hδ0.2)
      (by norm_num : (0 : ℝ) ≤ 6)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm0_lo : (5 : ℝ) ≤ m0 := by
    dsimp [m0]
    linarith [hm0_prod.1]
  have hm0_hi : m0 ≤ (8 : ℝ) := by
    dsimp [m0]
    linarith [hm0_prod.2]
  let s0 := (59 - m0) * (1 + δ 1)
  have hs0_exact_lo : (51 : ℝ) ≤ 59 - m0 := by linarith [hm0_hi]
  have hs0_exact_hi : 59 - m0 ≤ (54 : ℝ) := by linarith [hm0_lo]
  have hs0_prod :=
    mul_interval_mono hs0_exact_lo hs0_exact_hi
      (le_of_lt hδ1.1) (le_of_lt hδ1.2)
      (by norm_num : (0 : ℝ) ≤ 51)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs0_lo : (50 : ℝ) ≤ s0 := by
    dsimp [s0]
    linarith [hs0_prod.1]
  have hs0_hi : s0 ≤ (55 : ℝ) := by
    dsimp [s0]
    linarith [hs0_prod.2]
  let m1 := (x * s0) * (1 + δ 2)
  have hm1_prod :=
    mul_interval_mono hxb.1 hxb.2 hs0_lo hs0_hi
      (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
      (by norm_num : (0 : ℝ) ≤ 50)
  have hm1_exact_lo : (80 : ℝ) ≤ x * s0 := by linarith [hm1_prod.1]
  have hm1_exact_hi : x * s0 ≤ (89 : ℝ) := by linarith [hm1_prod.2]
  have hm1_prod_round :=
    mul_interval_mono hm1_exact_lo hm1_exact_hi
      (le_of_lt hδ2.1) (le_of_lt hδ2.2)
      (by norm_num : (0 : ℝ) ≤ 80)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm1_lo : (79 : ℝ) ≤ m1 := by
    dsimp [m1]
    linarith [hm1_prod_round.1]
  have hm1_hi : m1 ≤ (90 : ℝ) := by
    dsimp [m1]
    linarith [hm1_prod_round.2]
  let s1 := (324 - m1) * (1 + δ 3)
  have hs1_exact_lo : (234 : ℝ) ≤ 324 - m1 := by linarith [hm1_hi]
  have hs1_exact_hi : 324 - m1 ≤ (245 : ℝ) := by linarith [hm1_lo]
  have hs1_prod :=
    mul_interval_mono hs1_exact_lo hs1_exact_hi
      (le_of_lt hδ3.1) (le_of_lt hδ3.2)
      (by norm_num : (0 : ℝ) ≤ 234)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs1_lo : (233 : ℝ) ≤ s1 := by
    dsimp [s1]
    linarith [hs1_prod.1]
  have hs1_hi : s1 ≤ (246 : ℝ) := by
    dsimp [s1]
    linarith [hs1_prod.2]
  let m2 := (x * s1) * (1 + δ 4)
  have hm2_prod :=
    mul_interval_mono hxb.1 hxb.2 hs1_lo hs1_hi
      (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
      (by norm_num : (0 : ℝ) ≤ 233)
  have hm2_exact_lo : (374 : ℝ) ≤ x * s1 := by linarith [hm2_prod.1]
  have hm2_exact_hi : x * s1 ≤ (396 : ℝ) := by linarith [hm2_prod.2]
  have hm2_prod_round :=
    mul_interval_mono hm2_exact_lo hm2_exact_hi
      (le_of_lt hδ4.1) (le_of_lt hδ4.2)
      (by norm_num : (0 : ℝ) ≤ 374)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm2_lo : (373 : ℝ) ≤ m2 := by
    dsimp [m2]
    linarith [hm2_prod_round.1]
  have hm2_hi : m2 ≤ (397 : ℝ) := by
    dsimp [m2]
    linarith [hm2_prod_round.2]
  let s2 := (751 - m2) * (1 + δ 5)
  have hs2_exact_lo : (354 : ℝ) ≤ 751 - m2 := by linarith [hm2_hi]
  have hs2_exact_hi : 751 - m2 ≤ (378 : ℝ) := by linarith [hm2_lo]
  have hs2_prod :=
    mul_interval_mono hs2_exact_lo hs2_exact_hi
      (le_of_lt hδ5.1) (le_of_lt hδ5.2)
      (by norm_num : (0 : ℝ) ≤ 354)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs2_lo : (353 : ℝ) ≤ s2 := by
    dsimp [s2]
    linarith [hs2_prod.1]
  have hs2_hi : s2 ≤ (379 : ℝ) := by
    dsimp [s2]
    linarith [hs2_prod.2]
  let m3 := (x * s2) * (1 + δ 6)
  have hm3_prod :=
    mul_interval_mono hxb.1 hxb.2 hs2_lo hs2_hi
      (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
      (by norm_num : (0 : ℝ) ≤ 353)
  have hm3_exact_lo : (566 : ℝ) ≤ x * s2 := by linarith [hm3_prod.1]
  have hm3_exact_hi : x * s2 ≤ (610 : ℝ) := by linarith [hm3_prod.2]
  have hm3_prod_round :=
    mul_interval_mono hm3_exact_lo hm3_exact_hi
      (le_of_lt hδ6.1) (le_of_lt hδ6.2)
      (by norm_num : (0 : ℝ) ≤ 566)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm3_lo : (565 : ℝ) ≤ m3 := by
    dsimp [m3]
    linarith [hm3_prod_round.1]
  have hm3_hi : m3 ≤ (611 : ℝ) := by
    dsimp [m3]
    linarith [hm3_prod_round.2]
  let result := (622 - m3) * (1 + δ 7)
  have hresult_exact_lo : (11 : ℝ) ≤ 622 - m3 := by linarith [hm3_hi]
  have hresult_exact_hi : 622 - m3 ≤ (57 : ℝ) := by linarith [hm3_lo]
  have hresult_prod :=
    mul_interval_mono hresult_exact_lo hresult_exact_hi
      (le_of_lt hδ7.1) (le_of_lt hδ7.2)
      (by norm_num : (0 : ℝ) ≤ 11)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hresult_lo : (10 : ℝ) ≤ result := by
    dsimp [result]
    linarith [hresult_prod.1]
  have hresult_hi : result ≤ (58 : ℝ) := by
    dsimp [result]
    linarith [hresult_prod.2]
  simpa [kahanHornerNumeratorErrorEval, result, m3, s2, m2, s1, m1, s0, m0]
    using And.intro hresult_lo hresult_hi

set_option maxHeartbeats 800000 in
theorem kahanHornerDenominatorErrorEval_source_interval_bounds
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52)
    (δ : Fin 7 → ℝ) (hδ : ∀ i, |δ i| < kahanIeeeDoubleUnitRoundoff) :
    (999 : ℝ) / 1000 ≤ kahanHornerDenominatorErrorEval x δ ∧
      kahanHornerDenominatorErrorEval x δ ≤ 8 := by
  have hxb := kahan_source_interval_x_bounds hxlo hxhi
  have hδ0 := kahanIeeeDouble_delta_bounds (hδ 0)
  have hδ1 := kahanIeeeDouble_delta_bounds (hδ 1)
  have hδ2 := kahanIeeeDouble_delta_bounds (hδ 2)
  have hδ3 := kahanIeeeDouble_delta_bounds (hδ 3)
  have hδ4 := kahanIeeeDouble_delta_bounds (hδ 4)
  have hδ5 := kahanIeeeDouble_delta_bounds (hδ 5)
  have hδ6 := kahanIeeeDouble_delta_bounds (hδ 6)
  let s0 := (14 - x) * (1 + δ 0)
  have hs0_exact_lo : (1239 : ℝ) / 100 ≤ 14 - x := by linarith [hxb.2]
  have hs0_exact_hi : 14 - x ≤ (25 : ℝ) / 2 := by linarith [hxb.1]
  have hs0_prod :=
    mul_interval_mono hs0_exact_lo hs0_exact_hi
      (le_of_lt hδ0.1) (le_of_lt hδ0.2)
      (by norm_num : (0 : ℝ) ≤ (1239 : ℝ) / 100)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs0_lo : (123 : ℝ) / 10 ≤ s0 := by
    dsimp [s0]
    linarith [hs0_prod.1]
  have hs0_hi : s0 ≤ (63 : ℝ) / 5 := by
    dsimp [s0]
    linarith [hs0_prod.2]
  let m1 := (x * s0) * (1 + δ 1)
  have hm1_prod :=
    mul_interval_mono hxb.1 hxb.2 hs0_lo hs0_hi
      (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
      (by norm_num : (0 : ℝ) ≤ (123 : ℝ) / 10)
  have hm1_exact_lo : (197 : ℝ) / 10 ≤ x * s0 := by linarith [hm1_prod.1]
  have hm1_exact_hi : x * s0 ≤ (102 : ℝ) / 5 := by linarith [hm1_prod.2]
  have hm1_prod_round :=
    mul_interval_mono hm1_exact_lo hm1_exact_hi
      (le_of_lt hδ1.1) (le_of_lt hδ1.2)
      (by norm_num : (0 : ℝ) ≤ (197 : ℝ) / 10)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm1_lo : (98 : ℝ) / 5 ≤ m1 := by
    dsimp [m1]
    linarith [hm1_prod_round.1]
  have hm1_hi : m1 ≤ (103 : ℝ) / 5 := by
    dsimp [m1]
    linarith [hm1_prod_round.2]
  let s1 := (72 - m1) * (1 + δ 2)
  have hs1_exact_lo : (257 : ℝ) / 5 ≤ 72 - m1 := by linarith [hm1_hi]
  have hs1_exact_hi : 72 - m1 ≤ (262 : ℝ) / 5 := by linarith [hm1_lo]
  have hs1_prod :=
    mul_interval_mono hs1_exact_lo hs1_exact_hi
      (le_of_lt hδ2.1) (le_of_lt hδ2.2)
      (by norm_num : (0 : ℝ) ≤ (257 : ℝ) / 5)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs1_lo : (513 : ℝ) / 10 ≤ s1 := by
    dsimp [s1]
    linarith [hs1_prod.1]
  have hs1_hi : s1 ≤ (105 : ℝ) / 2 := by
    dsimp [s1]
    linarith [hs1_prod.2]
  let m2 := (x * s1) * (1 + δ 3)
  have hm2_prod :=
    mul_interval_mono hxb.1 hxb.2 hs1_lo hs1_hi
      (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
      (by norm_num : (0 : ℝ) ≤ (513 : ℝ) / 10)
  have hm2_exact_lo : (823 : ℝ) / 10 ≤ x * s1 := by linarith [hm2_prod.1]
  have hm2_exact_hi : x * s1 ≤ (422 : ℝ) / 5 := by linarith [hm2_prod.2]
  have hm2_prod_round :=
    mul_interval_mono hm2_exact_lo hm2_exact_hi
      (le_of_lt hδ3.1) (le_of_lt hδ3.2)
      (by norm_num : (0 : ℝ) ≤ (823 : ℝ) / 10)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm2_lo : (411 : ℝ) / 5 ≤ m2 := by
    dsimp [m2]
    linarith [hm2_prod_round.1]
  have hm2_hi : m2 ≤ (169 : ℝ) / 2 := by
    dsimp [m2]
    linarith [hm2_prod_round.2]
  let s2 := (151 - m2) * (1 + δ 4)
  have hs2_exact_lo : (133 : ℝ) / 2 ≤ 151 - m2 := by linarith [hm2_hi]
  have hs2_exact_hi : 151 - m2 ≤ (344 : ℝ) / 5 := by linarith [hm2_lo]
  have hs2_prod :=
    mul_interval_mono hs2_exact_lo hs2_exact_hi
      (le_of_lt hδ4.1) (le_of_lt hδ4.2)
      (by norm_num : (0 : ℝ) ≤ (133 : ℝ) / 2)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs2_lo : (332 : ℝ) / 5 ≤ s2 := by
    dsimp [s2]
    linarith [hs2_prod.1]
  have hs2_hi : s2 ≤ (689 : ℝ) / 10 := by
    dsimp [s2]
    linarith [hs2_prod.2]
  let m3 := (x * s2) * (1 + δ 5)
  have hm3_prod :=
    mul_interval_mono hxb.1 hxb.2 hs2_lo hs2_hi
      (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
      (by norm_num : (0 : ℝ) ≤ (332 : ℝ) / 5)
  have hm3_exact_lo : (106 : ℝ) ≤ x * s2 := by linarith [hm3_prod.1]
  have hm3_exact_hi : x * s2 ≤ (554 : ℝ) / 5 := by linarith [hm3_prod.2]
  have hm3_prod_round :=
    mul_interval_mono hm3_exact_lo hm3_exact_hi
      (le_of_lt hδ5.1) (le_of_lt hδ5.2)
      (by norm_num : (0 : ℝ) ≤ 106)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm3_lo : (105 : ℝ) ≤ m3 := by
    dsimp [m3]
    linarith [hm3_prod_round.1]
  have hm3_hi : m3 ≤ (111 : ℝ) := by
    dsimp [m3]
    linarith [hm3_prod_round.2]
  let result := (112 - m3) * (1 + δ 6)
  have hresult_exact_lo : (1 : ℝ) ≤ 112 - m3 := by linarith [hm3_hi]
  have hresult_exact_hi : 112 - m3 ≤ (7 : ℝ) := by linarith [hm3_lo]
  have hresult_prod :=
    mul_interval_mono hresult_exact_lo hresult_exact_hi
      (le_of_lt hδ6.1) (le_of_lt hδ6.2)
      (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hresult_lo : (999 : ℝ) / 1000 ≤ result := by
    dsimp [result]
    linarith [hresult_prod.1]
  have hresult_hi : result ≤ (8 : ℝ) := by
    dsimp [result]
    linarith [hresult_prod.2]
  simpa [kahanHornerDenominatorErrorEval, result, m3, s2, m2, s1, m1, s0]
    using And.intro hresult_lo hresult_hi

/-- The numerator IEEE-double Horner trace is finite-normal on every point of
the source interval used for Figure 1.6. -/
theorem ieeeDoubleKahanHornerNumerator_eq_errorEval_on_source_interval
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    ∃ δ : Fin 8 → ℝ,
      (∀ i, |δ i| < kahanIeeeDoubleUnitRoundoff) ∧
        ieeeDoubleKahanHornerNumerator x =
          kahanHornerNumeratorErrorEval x δ :=
  ieeeDoubleKahanHornerNumerator_eq_errorEval_of_finiteNormal x
    (ieeeDoubleKahanNumeratorNormalTrace_of_source_interval hxlo hxhi)

/-- The denominator IEEE-double Horner trace is finite-normal on every point of
the source interval used for Figure 1.6. -/
theorem ieeeDoubleKahanHornerDenominator_eq_errorEval_on_source_interval
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    ∃ δ : Fin 7 → ℝ,
      (∀ i, |δ i| < kahanIeeeDoubleUnitRoundoff) ∧
        ieeeDoubleKahanHornerDenominator x =
          kahanHornerDenominatorErrorEval x δ :=
  ieeeDoubleKahanHornerDenominator_eq_errorEval_of_finiteNormal x
    (ieeeDoubleKahanDenominatorNormalTrace_of_source_interval hxlo hxhi)

theorem ieeeDoubleKahanHornerNumerator_source_interval_bounds
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    (10 : ℝ) ≤ ieeeDoubleKahanHornerNumerator x ∧
      ieeeDoubleKahanHornerNumerator x ≤ 58 := by
  rcases ieeeDoubleKahanHornerNumerator_eq_errorEval_on_source_interval
      hxlo hxhi with ⟨δ, hδ, hnum⟩
  have hbounds :=
    kahanHornerNumeratorErrorEval_source_interval_bounds hxlo hxhi δ hδ
  rw [hnum]
  exact hbounds

theorem ieeeDoubleKahanHornerDenominator_source_interval_bounds
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    (999 : ℝ) / 1000 ≤ ieeeDoubleKahanHornerDenominator x ∧
      ieeeDoubleKahanHornerDenominator x ≤ 8 := by
  rcases ieeeDoubleKahanHornerDenominator_eq_errorEval_on_source_interval
      hxlo hxhi with ⟨δ, hδ, hden⟩
  have hbounds :=
    kahanHornerDenominatorErrorEval_source_interval_bounds hxlo hxhi δ hδ
  rw [hden]
  exact hbounds

theorem ieeeDoubleKahanQuotientNormalTrace_of_source_interval
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    IeeeDoubleKahanQuotientNormalTrace x := by
  have hnumTrace := ieeeDoubleKahanNumeratorNormalTrace_of_source_interval hxlo hxhi
  have hdenTrace := ieeeDoubleKahanDenominatorNormalTrace_of_source_interval hxlo hxhi
  have hnumBounds := ieeeDoubleKahanHornerNumerator_source_interval_bounds hxlo hxhi
  have hdenBounds := ieeeDoubleKahanHornerDenominator_source_interval_bounds hxlo hxhi
  have hdenPos : 0 < ieeeDoubleKahanHornerDenominator x := by
    nlinarith [hdenBounds.1]
  refine
    { numerator := hnumTrace
      denominator := hdenTrace
      quotient := ?_ }
  apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
  · simp [BasicOp.exact]
    rw [le_div_iff₀ hdenPos]
    linarith [hnumBounds.1, hdenBounds.2]
  · simp [BasicOp.exact]
    rw [div_le_iff₀ hdenPos]
    nlinarith [hnumBounds.2, hdenBounds.1]

theorem ieeeDoubleKahanRationalFunction_eq_errorEval_on_source_interval
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    ∃ δN : Fin 8 → ℝ, ∃ δD : Fin 7 → ℝ, ∃ δq : ℝ,
      (∀ i, |δN i| < kahanIeeeDoubleUnitRoundoff) ∧
      (∀ i, |δD i| < kahanIeeeDoubleUnitRoundoff) ∧
      |δq| < kahanIeeeDoubleUnitRoundoff ∧
        ieeeDoubleKahanRationalFunction x =
          (kahanHornerNumeratorErrorEval x δN /
            kahanHornerDenominatorErrorEval x δD) * (1 + δq) :=
  ieeeDoubleKahanRationalFunction_eq_errorEval_of_finiteNormal x
    (ieeeDoubleKahanQuotientNormalTrace_of_source_interval hxlo hxhi)

/-- The numerator is the quartic polynomial displayed by the Horner form. -/
theorem kahanHornerNumerator_eq_poly (x : ℝ) :
    kahanHornerNumerator x =
      622 - 751 * x + 324 * x ^ 2 - 59 * x ^ 3 + 4 * x ^ 4 := by
  unfold kahanHornerNumerator
  ring

/-- The denominator is the quartic polynomial displayed by the Horner form. -/
theorem kahanHornerDenominator_eq_poly (x : ℝ) :
    kahanHornerDenominator x =
      112 - 151 * x + 72 * x ^ 2 - 14 * x ^ 3 + x ^ 4 := by
  unfold kahanHornerDenominator
  ring

/-- The denominator expanded around the first source grid point `1.606`. -/
theorem kahanHornerDenominator_shifted_eq (t : ℝ) :
    kahanHornerDenominator ((803 : ℝ) / 500 + t) =
      241244257481 / 62500000000 -
        359215623 / 31250000 * t +
        2502927 / 125000 * t ^ 2 -
        947 / 125 * t ^ 3 + t ^ 4 := by
  rw [kahanHornerDenominator_eq_poly]
  ring

/-- The numerator expanded around the first source grid point `1.606`. -/
theorem kahanHornerNumerator_shifted_eq (t : ℝ) :
    kahanHornerNumerator ((803 : ℝ) / 500 + t) =
      131966286839 / 3906250000 -
        3142522617 / 31250000 * t +
        6352479 / 62500 * t ^ 2 -
        4163 / 125 * t ^ 3 + 4 * t ^ 4 := by
  rw [kahanHornerNumerator_eq_poly]
  ring

/-- Source grid point `x = 1.606 + (k-1) * 2^-52`, with source indexing. -/
noncomputable def kahanHornerGridPoint (k : ℕ) : ℝ :=
  (803 : ℝ) / 500 + ((k : ℝ) - 1) / (2 : ℝ) ^ 52

/-- The first source grid point, `k = 1`, is `1.606`. -/
theorem kahanHornerGridPoint_one :
    kahanHornerGridPoint 1 = (803 : ℝ) / 500 := by
  norm_num [kahanHornerGridPoint]

/-- Consecutive source grid points are separated by `2^-52`. -/
theorem kahanHornerGridPoint_succ_sub (k : ℕ) :
    kahanHornerGridPoint (k + 1) - kahanHornerGridPoint k =
      1 / (2 : ℝ) ^ 52 := by
  unfold kahanHornerGridPoint
  rw [Nat.cast_add, Nat.cast_one]
  ring

/-- The final source grid point for `k = 361`. -/
theorem kahanHornerGridPoint_three_sixty_one :
    kahanHornerGridPoint 361 =
      (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52 := by
  norm_num [kahanHornerGridPoint]

/-- Every source grid point lies in the sampled interval starting at `1.606`
and ending at `1.606 + 360*2^-52`. -/
theorem kahanHornerGridPoint_mem_source_interval
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    0 ≤ kahanHornerGridPoint k - (803 : ℝ) / 500 ∧
      kahanHornerGridPoint k - (803 : ℝ) / 500 ≤ 360 / (2 : ℝ) ^ 52 := by
  unfold kahanHornerGridPoint
  constructor
  · have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    nlinarith
  · have hk361R : (k : ℝ) ≤ 361 := by exact_mod_cast hk361
    nlinarith

/-- Any two of the 361 source grid points are at most the full source
interval width apart. -/
theorem kahanHornerGridPoint_pairwise_distance_le_source_width
    (k l : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361)
    (hl1 : 1 ≤ l) (hl361 : l ≤ 361) :
    |kahanHornerGridPoint k - kahanHornerGridPoint l| ≤
      360 / (2 : ℝ) ^ 52 := by
  have hk := kahanHornerGridPoint_mem_source_interval k hk1 hk361
  have hl := kahanHornerGridPoint_mem_source_interval l hl1 hl361
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- Source-grid specialization of the finite-normal numerator certificate. -/
theorem ieeeDoubleKahanNumeratorNormalTrace_of_source_grid
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    IeeeDoubleKahanNumeratorNormalTrace (kahanHornerGridPoint k) := by
  have hmem := kahanHornerGridPoint_mem_source_interval k hk1 hk361
  apply ieeeDoubleKahanNumeratorNormalTrace_of_source_interval
  · linarith [hmem.1]
  · linarith [hmem.2]

/-- Source-grid specialization of the finite-normal denominator certificate. -/
theorem ieeeDoubleKahanDenominatorNormalTrace_of_source_grid
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    IeeeDoubleKahanDenominatorNormalTrace (kahanHornerGridPoint k) := by
  have hmem := kahanHornerGridPoint_mem_source_interval k hk1 hk361
  apply ieeeDoubleKahanDenominatorNormalTrace_of_source_interval
  · linarith [hmem.1]
  · linarith [hmem.2]

/-- Source-grid specialization of the IEEE-double numerator local-error
expansion. -/
theorem ieeeDoubleKahanHornerNumerator_grid_eq_errorEval
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    ∃ δ : Fin 8 → ℝ,
      (∀ i, |δ i| < kahanIeeeDoubleUnitRoundoff) ∧
        ieeeDoubleKahanHornerNumerator (kahanHornerGridPoint k) =
          kahanHornerNumeratorErrorEval (kahanHornerGridPoint k) δ :=
  ieeeDoubleKahanHornerNumerator_eq_errorEval_of_finiteNormal
    (kahanHornerGridPoint k)
    (ieeeDoubleKahanNumeratorNormalTrace_of_source_grid k hk1 hk361)

/-- Source-grid specialization of the IEEE-double denominator local-error
expansion. -/
theorem ieeeDoubleKahanHornerDenominator_grid_eq_errorEval
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    ∃ δ : Fin 7 → ℝ,
      (∀ i, |δ i| < kahanIeeeDoubleUnitRoundoff) ∧
        ieeeDoubleKahanHornerDenominator (kahanHornerGridPoint k) =
          kahanHornerDenominatorErrorEval (kahanHornerGridPoint k) δ :=
  ieeeDoubleKahanHornerDenominator_eq_errorEval_of_finiteNormal
    (kahanHornerGridPoint k)
    (ieeeDoubleKahanDenominatorNormalTrace_of_source_grid k hk1 hk361)

/-- Source-grid specialization of the complete IEEE-double quotient
finite-normal certificate. -/
theorem ieeeDoubleKahanQuotientNormalTrace_of_source_grid
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    IeeeDoubleKahanQuotientNormalTrace (kahanHornerGridPoint k) := by
  have hmem := kahanHornerGridPoint_mem_source_interval k hk1 hk361
  apply ieeeDoubleKahanQuotientNormalTrace_of_source_interval
  · linarith [hmem.1]
  · linarith [hmem.2]

/-- Source-grid specialization of the full IEEE-double rounded rational-function
local-error expansion, including the final rounded division. -/
theorem ieeeDoubleKahanRationalFunction_grid_eq_errorEval
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    ∃ δN : Fin 8 → ℝ, ∃ δD : Fin 7 → ℝ, ∃ δq : ℝ,
      (∀ i, |δN i| < kahanIeeeDoubleUnitRoundoff) ∧
      (∀ i, |δD i| < kahanIeeeDoubleUnitRoundoff) ∧
      |δq| < kahanIeeeDoubleUnitRoundoff ∧
        ieeeDoubleKahanRationalFunction (kahanHornerGridPoint k) =
          (kahanHornerNumeratorErrorEval (kahanHornerGridPoint k) δN /
            kahanHornerDenominatorErrorEval (kahanHornerGridPoint k) δD) *
              (1 + δq) :=
  ieeeDoubleKahanRationalFunction_eq_errorEval_of_finiteNormal
    (kahanHornerGridPoint k)
    (ieeeDoubleKahanQuotientNormalTrace_of_source_grid k hk1 hk361)

/-- At the first grid point the exact denominator is positive. -/
theorem kahanHornerDenominator_grid_one_pos :
    0 < kahanHornerDenominator (kahanHornerGridPoint 1) := by
  norm_num [kahanHornerGridPoint_one, kahanHornerDenominator]

/-- On the source grid interval the exact denominator is bounded away from
zero by the simple lower bound `3`. -/
theorem kahanHornerDenominator_gt_three_on_source_grid_interval (t : ℝ)
    (_ht0 : 0 ≤ t) (ht : t ≤ 360 / (2 : ℝ) ^ 52) :
    3 < kahanHornerDenominator ((803 : ℝ) / 500 + t) := by
  rw [kahanHornerDenominator_shifted_eq]
  nlinarith [ht]

/-- The exact denominator is positive on the whole source grid interval
`1.606 <= x <= 1.606 + 360*2^-52`. -/
theorem kahanHornerDenominator_pos_on_source_grid_interval (t : ℝ)
    (_ht0 : 0 ≤ t) (ht : t ≤ 360 / (2 : ℝ) ^ 52) :
    0 < kahanHornerDenominator ((803 : ℝ) / 500 + t) := by
  rw [kahanHornerDenominator_shifted_eq]
  nlinarith [ht]

/-- The exact denominator is positive at every one of the 361 source grid
points used in Figure 1.6. -/
theorem kahanHornerDenominator_grid_pos_of_one_le_of_le_three_sixty_one
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    0 < kahanHornerDenominator (kahanHornerGridPoint k) := by
  unfold kahanHornerGridPoint
  apply kahanHornerDenominator_pos_on_source_grid_interval
  · have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    exact div_nonneg (sub_nonneg.mpr hk1R) (by positivity)
  · have hk361R : (k : ℝ) ≤ 361 := by exact_mod_cast hk361
    have hnum : (k : ℝ) - 1 ≤ 360 := by linarith
    exact div_le_div_of_nonneg_right hnum (by positivity)

/-- Exact Euclidean-algorithm identity behind the continued-fraction
reference curve.  The hypotheses are precisely the nonzero intermediate
denominators generated by the continued fraction and the displayed rational
function denominator. -/
theorem kahanContinuedFraction_eq_rationalFunction (x : ℝ)
    (h0 : x - 3 ≠ 0)
    (hp2 : kahanContinuedFractionP2 x ≠ 0)
    (hp1 : kahanContinuedFractionP1 x ≠ 0)
    (hD : kahanHornerDenominator x ≠ 0) :
    kahanContinuedFraction x = kahanRationalFunction x := by
  have htail1 :
      kahanContinuedFractionTail1 x =
        kahanContinuedFractionP2 x / (x - 3) := by
    unfold kahanContinuedFractionTail1 kahanContinuedFractionP2
    field_simp [h0]
    ring
  have htail2 :
      kahanContinuedFractionTail2 x =
        kahanContinuedFractionP1 x / kahanContinuedFractionP2 x := by
    unfold kahanContinuedFractionTail2
    rw [htail1]
    field_simp [h0, hp2]
    unfold kahanContinuedFractionP1 kahanContinuedFractionP2
    ring_nf
  have htail3 :
      kahanContinuedFractionTail3 x =
        kahanHornerDenominator x / kahanContinuedFractionP1 x := by
    unfold kahanContinuedFractionTail3
    rw [htail2, kahanHornerDenominator_eq_poly]
    field_simp [hp1, hp2]
    unfold kahanContinuedFractionP1 kahanContinuedFractionP2
    ring_nf
    norm_num
    rfl
  have hnum :
      4 * kahanHornerDenominator x - 3 * kahanContinuedFractionP1 x =
        kahanHornerNumerator x := by
    rw [kahanHornerNumerator_eq_poly, kahanHornerDenominator_eq_poly]
    unfold kahanContinuedFractionP1
    ring
  unfold kahanContinuedFraction kahanRationalFunction
  rw [htail3]
  calc
    4 - 3 / (kahanHornerDenominator x / kahanContinuedFractionP1 x)
        = (4 * kahanHornerDenominator x -
              3 * kahanContinuedFractionP1 x) /
            kahanHornerDenominator x := by
          field_simp [hp1, hD]
    _ = kahanHornerNumerator x / kahanHornerDenominator x := by
          rw [hnum]

/-- On the source interval, the quadratic continued-fraction denominator is
bounded away from zero. -/
theorem kahanContinuedFractionP2_neg_on_source_interval
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    kahanContinuedFractionP2 x < 0 := by
  unfold kahanContinuedFractionP2
  nlinarith [hxlo, hxhi]

/-- On the source interval, the cubic continued-fraction denominator is
bounded away from zero. -/
theorem kahanContinuedFractionP1_neg_on_source_interval
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    kahanContinuedFractionP1 x < 0 := by
  unfold kahanContinuedFractionP1
  nlinarith [hxlo, hxhi]

/-- The continued-fraction reference expression equals the exact rational
function throughout the full source interval used for Figure 1.6. -/
theorem kahanContinuedFraction_eq_rationalFunction_on_source_interval
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    kahanContinuedFraction x = kahanRationalFunction x := by
  have h0 : x - 3 ≠ 0 := by nlinarith
  have hp2 : kahanContinuedFractionP2 x ≠ 0 :=
    ne_of_lt (kahanContinuedFractionP2_neg_on_source_interval hxlo hxhi)
  have hp1 : kahanContinuedFractionP1 x ≠ 0 :=
    ne_of_lt (kahanContinuedFractionP1_neg_on_source_interval hxlo hxhi)
  have ht0 : 0 ≤ x - (803 : ℝ) / 500 := by linarith
  have htw : x - (803 : ℝ) / 500 ≤ 360 / (2 : ℝ) ^ 52 := by linarith
  have hDpos :=
    kahanHornerDenominator_pos_on_source_grid_interval
      (x - (803 : ℝ) / 500) ht0 htw
  have harg : (803 : ℝ) / 500 + (x - (803 : ℝ) / 500) = x := by ring
  rw [harg] at hDpos
  exact kahanContinuedFraction_eq_rationalFunction x h0 hp2 hp1
    (ne_of_gt hDpos)

/-- Source-grid specialization of the exact continued-fraction reference
identity. -/
theorem kahanContinuedFraction_grid_eq_rationalFunction
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    kahanContinuedFraction (kahanHornerGridPoint k) =
      kahanRationalFunction (kahanHornerGridPoint k) := by
  have hmem := kahanHornerGridPoint_mem_source_interval k hk1 hk361
  apply kahanContinuedFraction_eq_rationalFunction_on_source_interval
  · linarith [hmem.1]
  · linarith [hmem.2]

/-- Cubic kernel for the exact numerator difference
`r(1.606+t)-r(1.606)` after clearing denominators. -/
noncomputable def kahanRationalFunctionFirstDiffKernel (t : ℝ) : ℝ :=
  (-2292967119 / 125000000 : ℝ) * t ^ 3 +
    (7962026674329 / 62500000000 : ℝ) * t ^ 2 -
    (8879334238671813 / 31250000000000 : ℝ) * t +
    (2832765715803387 / 15625000000000000 : ℝ)

/-- On the tiny source interval, the exact first-difference kernel is bounded
by `1`.  This is deliberately conservative; it keeps the all-grid reference
curve proof parametric instead of checking the 361 points one by one. -/
theorem kahanRationalFunctionFirstDiffKernel_abs_lt_one
    (t : ℝ) (ht0 : 0 ≤ t) (htw : t ≤ 360 / (2 : ℝ) ^ 52) :
    |kahanRationalFunctionFirstDiffKernel t| < 1 := by
  unfold kahanRationalFunctionFirstDiffKernel
  rw [abs_lt]
  constructor <;> nlinarith [ht0, htw]

/-- Exact cleared-denominator factorization for the change from the first
source grid point to `1.606+t`. -/
theorem kahanRationalFunction_first_diff_num_factor (t : ℝ) :
    kahanHornerNumerator ((803 : ℝ) / 500 + t) *
          kahanHornerDenominator ((803 : ℝ) / 500) -
        kahanHornerNumerator ((803 : ℝ) / 500) *
          kahanHornerDenominator ((803 : ℝ) / 500 + t) =
      t * kahanRationalFunctionFirstDiffKernel t := by
  rw [kahanHornerNumerator_shifted_eq, kahanHornerDenominator_shifted_eq]
  norm_num [kahanRationalFunctionFirstDiffKernel, kahanHornerNumerator,
    kahanHornerDenominator]
  ring

/-- The exact reference rational function is virtually constant throughout the
whole source interval, relative to the first source grid point.  This is exact
real arithmetic only; it does not model double-precision Horner evaluation. -/
theorem kahanRationalFunction_source_interval_variation_from_first_lt
    (t : ℝ) (ht0 : 0 ≤ t) (htw : t ≤ 360 / (2 : ℝ) ^ 52) :
    |kahanRationalFunction ((803 : ℝ) / 500 + t) -
        kahanRationalFunction ((803 : ℝ) / 500)| < (1 : ℝ) / 10 ^ 12 := by
  have hD0 : 0 < kahanHornerDenominator ((803 : ℝ) / 500) := by
    norm_num [kahanHornerDenominator]
  have hDt : 0 < kahanHornerDenominator ((803 : ℝ) / 500 + t) :=
    kahanHornerDenominator_pos_on_source_grid_interval t ht0 htw
  simp only [kahanRationalFunction]
  rw [div_sub_div]
  · rw [abs_div]
    have hnum :
        |kahanHornerNumerator ((803 : ℝ) / 500 + t) *
              kahanHornerDenominator ((803 : ℝ) / 500) -
            kahanHornerNumerator ((803 : ℝ) / 500) *
              kahanHornerDenominator ((803 : ℝ) / 500 + t)|
          < (1 / 10 ^ 12) *
              |kahanHornerDenominator ((803 : ℝ) / 500 + t) *
                kahanHornerDenominator ((803 : ℝ) / 500)| := by
      rw [kahanRationalFunction_first_diff_num_factor t]
      rw [abs_mul, abs_of_nonneg ht0]
      have hkernel := kahanRationalFunctionFirstDiffKernel_abs_lt_one t ht0 htw
      have hnum_le :
          t * |kahanRationalFunctionFirstDiffKernel t| ≤ t := by
        exact mul_le_of_le_one_right ht0 (le_of_lt hkernel)
      have hDt3 :
          3 < kahanHornerDenominator ((803 : ℝ) / 500 + t) :=
        kahanHornerDenominator_gt_three_on_source_grid_interval t ht0 htw
      have hD03 : (3 : ℝ) < kahanHornerDenominator ((803 : ℝ) / 500) := by
        norm_num [kahanHornerDenominator]
      have hprod_abs :
          |kahanHornerDenominator ((803 : ℝ) / 500 + t) *
              kahanHornerDenominator ((803 : ℝ) / 500)| =
            kahanHornerDenominator ((803 : ℝ) / 500 + t) *
              kahanHornerDenominator ((803 : ℝ) / 500) := by
        exact abs_of_pos (mul_pos hDt hD0)
      rw [hprod_abs]
      have ht_target :
          t < (1 / 10 ^ 12) *
              (kahanHornerDenominator ((803 : ℝ) / 500 + t) *
                kahanHornerDenominator ((803 : ℝ) / 500)) := by
        nlinarith [htw, hDt3, hD03]
      exact lt_of_le_of_lt hnum_le ht_target
    have hdenAbsPos :
        0 < |kahanHornerDenominator ((803 : ℝ) / 500 + t) *
              kahanHornerDenominator ((803 : ℝ) / 500)| :=
      abs_pos.mpr (mul_ne_zero (ne_of_gt hDt) (ne_of_gt hD0))
    rw [div_lt_iff₀ hdenAbsPos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hnum
  · exact ne_of_gt hDt
  · exact ne_of_gt hD0

/-- Every one of the 361 exact source-grid reference values is within
`10^-12` of the first reference value. -/
theorem kahanRationalFunction_grid_variation_from_first_lt
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    |kahanRationalFunction (kahanHornerGridPoint k) -
        kahanRationalFunction (kahanHornerGridPoint 1)| < (1 : ℝ) / 10 ^ 12 := by
  have hmem := kahanHornerGridPoint_mem_source_interval k hk1 hk361
  have h :=
    kahanRationalFunction_source_interval_variation_from_first_lt
      (kahanHornerGridPoint k - (803 : ℝ) / 500) hmem.1 hmem.2
  have harg :
      (803 : ℝ) / 500 + (kahanHornerGridPoint k - (803 : ℝ) / 500) =
        kahanHornerGridPoint k := by
    ring
  rw [harg, ← kahanHornerGridPoint_one] at h
  exact h

/-- Every one of the 361 continued-fraction reference values is within
`10^-12` of the first continued-fraction reference value. -/
theorem kahanContinuedFraction_grid_variation_from_first_lt
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    |kahanContinuedFraction (kahanHornerGridPoint k) -
        kahanContinuedFraction (kahanHornerGridPoint 1)| < (1 : ℝ) / 10 ^ 12 := by
  rw [kahanContinuedFraction_grid_eq_rationalFunction k hk1 hk361,
    kahanContinuedFraction_grid_eq_rationalFunction 1 (by norm_num) (by norm_num)]
  exact kahanRationalFunction_grid_variation_from_first_lt k hk1 hk361

/-- Any two of the 361 exact source-grid reference values differ by less than
`2*10^-12`.  This closes the all-grid exact-reference part of the statement
that the reference curve is virtually constant; it is not a rounded Horner
evaluation theorem. -/
theorem kahanRationalFunction_grid_pair_variation_lt_two
    (k l : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361)
    (hl1 : 1 ≤ l) (hl361 : l ≤ 361) :
    |kahanRationalFunction (kahanHornerGridPoint k) -
        kahanRationalFunction (kahanHornerGridPoint l)| <
      (2 : ℝ) / 10 ^ 12 := by
  have hk := kahanRationalFunction_grid_variation_from_first_lt k hk1 hk361
  have hl := kahanRationalFunction_grid_variation_from_first_lt l hl1 hl361
  have htri :
      |kahanRationalFunction (kahanHornerGridPoint k) -
          kahanRationalFunction (kahanHornerGridPoint l)| ≤
        |kahanRationalFunction (kahanHornerGridPoint k) -
          kahanRationalFunction (kahanHornerGridPoint 1)| +
        |kahanRationalFunction (kahanHornerGridPoint l) -
          kahanRationalFunction (kahanHornerGridPoint 1)| := by
    calc
      |kahanRationalFunction (kahanHornerGridPoint k) -
          kahanRationalFunction (kahanHornerGridPoint l)|
          = |(kahanRationalFunction (kahanHornerGridPoint k) -
                kahanRationalFunction (kahanHornerGridPoint 1)) +
              (kahanRationalFunction (kahanHornerGridPoint 1) -
                kahanRationalFunction (kahanHornerGridPoint l))| := by ring_nf
      _ ≤ |kahanRationalFunction (kahanHornerGridPoint k) -
              kahanRationalFunction (kahanHornerGridPoint 1)| +
            |kahanRationalFunction (kahanHornerGridPoint 1) -
              kahanRationalFunction (kahanHornerGridPoint l)| := abs_add_le _ _
      _ =
          |kahanRationalFunction (kahanHornerGridPoint k) -
              kahanRationalFunction (kahanHornerGridPoint 1)| +
            |kahanRationalFunction (kahanHornerGridPoint l) -
              kahanRationalFunction (kahanHornerGridPoint 1)| := by
            rw [abs_sub_comm
              (kahanRationalFunction (kahanHornerGridPoint 1))
              (kahanRationalFunction (kahanHornerGridPoint l))]
  nlinarith

/-- Figure 1.6 diagnostic bridge.  Since the exact reference values on the
source grid differ by less than `2*10^-12`, any supplied rounded values whose
spread exceeds that reference spread by `η` must have rounding-error values
whose spread exceeds `η`.  This packages the nonrandom-pattern comparison
without enumerating the plotted IEEE-double values. -/
theorem kahanRoundedGrid_error_spread_gt_of_output_spread
    (rounded : ℕ → ℝ) (k l : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361)
    (hl1 : 1 ≤ l) (hl361 : l ≤ 361) (η : ℝ)
    (hspread :
      (2 : ℝ) / 10 ^ 12 + η < |rounded k - rounded l|) :
    η <
      |(rounded k - kahanRationalFunction (kahanHornerGridPoint k)) -
        (rounded l - kahanRationalFunction (kahanHornerGridPoint l))| := by
  set exactK : ℝ := kahanRationalFunction (kahanHornerGridPoint k)
  set exactL : ℝ := kahanRationalFunction (kahanHornerGridPoint l)
  set errDiff : ℝ := (rounded k - exactK) - (rounded l - exactL)
  have hexact :
      |exactK - exactL| < (2 : ℝ) / 10 ^ 12 := by
    simpa [exactK, exactL] using
      kahanRationalFunction_grid_pair_variation_lt_two
        k l hk1 hk361 hl1 hl361
  have htri :
      |rounded k - rounded l| ≤ |errDiff| + |exactK - exactL| := by
    calc
      |rounded k - rounded l|
          = |errDiff + (exactK - exactL)| := by
              simp [errDiff]
              ring_nf
      _ ≤ |errDiff| + |exactK - exactL| := abs_add_le _ _
  by_contra hnot
  have herr : |errDiff| ≤ η := le_of_not_gt hnot
  have hle : |rounded k - rounded l| ≤ η + (2 : ℝ) / 10 ^ 12 := by
    nlinarith
  nlinarith

/-- The same Figure 1.6 diagnostic bridge specialized to the concrete
IEEE-double finite round-to-even Horner path already modeled in this file.  A
future proof of a visible rounded-output spread can feed this theorem directly;
the theorem itself still avoids enumerating the 361 plotted values. -/
theorem ieeeDoubleKahanRationalFunction_grid_error_spread_gt_of_output_spread
    (k l : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361)
    (hl1 : 1 ≤ l) (hl361 : l ≤ 361) (η : ℝ)
    (hspread :
      (2 : ℝ) / 10 ^ 12 + η <
        |ieeeDoubleKahanRationalFunction (kahanHornerGridPoint k) -
          ieeeDoubleKahanRationalFunction (kahanHornerGridPoint l)|) :
    η <
      |(ieeeDoubleKahanRationalFunction (kahanHornerGridPoint k) -
          kahanRationalFunction (kahanHornerGridPoint k)) -
        (ieeeDoubleKahanRationalFunction (kahanHornerGridPoint l) -
          kahanRationalFunction (kahanHornerGridPoint l))| := by
  exact
    kahanRoundedGrid_error_spread_gt_of_output_spread
      (fun j => ieeeDoubleKahanRationalFunction (kahanHornerGridPoint j))
      k l hk1 hk361 hl1 hl361 η hspread

/-- The exact rational function changes by less than `10^-12` between the
first and last source grid points. This is a conservative exact-arithmetic
substrate for the PDF's statement that the reference curve is virtually
constant on the tiny sampled interval; it is not a Horner rounding theorem. -/
theorem kahanRationalFunction_first_to_last_variation_lt :
    |kahanRationalFunction (kahanHornerGridPoint 361) -
        kahanRationalFunction (kahanHornerGridPoint 1)| < (1 : ℝ) / 10 ^ 12 := by
  norm_num [kahanRationalFunction, kahanHornerGridPoint,
    kahanHornerNumerator, kahanHornerDenominator]

/-- Endpoint version of the Figure 1.6 diagnostic bridge.  The exact
first-to-last reference spread is below `10^-12`, so a supplied rounded
endpoint spread exceeding that by `η` forces the rounded-error endpoints to
differ by more than `η`. -/
theorem kahanRoundedGrid_endpoint_error_spread_gt_of_output_spread
    (rounded : ℕ → ℝ) (η : ℝ)
    (hspread :
      (1 : ℝ) / 10 ^ 12 + η < |rounded 361 - rounded 1|) :
    η <
      |(rounded 361 - kahanRationalFunction (kahanHornerGridPoint 361)) -
        (rounded 1 - kahanRationalFunction (kahanHornerGridPoint 1))| := by
  set exactLast : ℝ := kahanRationalFunction (kahanHornerGridPoint 361)
  set exactFirst : ℝ := kahanRationalFunction (kahanHornerGridPoint 1)
  set errDiff : ℝ := (rounded 361 - exactLast) - (rounded 1 - exactFirst)
  have hexact :
      |exactLast - exactFirst| < (1 : ℝ) / 10 ^ 12 := by
    simpa [exactLast, exactFirst] using
      kahanRationalFunction_first_to_last_variation_lt
  have htri :
      |rounded 361 - rounded 1| ≤ |errDiff| + |exactLast - exactFirst| := by
    calc
      |rounded 361 - rounded 1|
          = |errDiff + (exactLast - exactFirst)| := by
              simp [errDiff]
              ring_nf
      _ ≤ |errDiff| + |exactLast - exactFirst| := abs_add_le _ _
  by_contra hnot
  have herr : |errDiff| ≤ η := le_of_not_gt hnot
  have hle : |rounded 361 - rounded 1| ≤ η + (1 : ℝ) / 10 ^ 12 := by
    nlinarith
  nlinarith

/-- Endpoint Figure 1.6 diagnostic bridge specialized to the concrete
IEEE-double finite round-to-even Horner path. -/
theorem ieeeDoubleKahanRationalFunction_endpoint_error_spread_gt_of_output_spread
    (η : ℝ)
    (hspread :
      (1 : ℝ) / 10 ^ 12 + η <
        |ieeeDoubleKahanRationalFunction (kahanHornerGridPoint 361) -
          ieeeDoubleKahanRationalFunction (kahanHornerGridPoint 1)|) :
    η <
      |(ieeeDoubleKahanRationalFunction (kahanHornerGridPoint 361) -
          kahanRationalFunction (kahanHornerGridPoint 361)) -
        (ieeeDoubleKahanRationalFunction (kahanHornerGridPoint 1) -
          kahanRationalFunction (kahanHornerGridPoint 1))| := by
  exact
    kahanRoundedGrid_endpoint_error_spread_gt_of_output_spread
      (fun j => ieeeDoubleKahanRationalFunction (kahanHornerGridPoint j))
      η hspread

/-- The exact reference spread between the selected grid points `175` and
`289` is below `10^-15`.  These are the two grid indices used for the compact
two-point Figure 1.6 diagnostic route. -/
theorem kahanRationalFunction_grid_175_289_variation_lt_one_e15 :
    |kahanRationalFunction (kahanHornerGridPoint 289) -
        kahanRationalFunction (kahanHornerGridPoint 175)| < (1 : ℝ) / 10 ^ 15 := by
  norm_num [kahanRationalFunction, kahanHornerGridPoint,
    kahanHornerNumerator, kahanHornerDenominator]

/-- Two-point Figure 1.6 diagnostic bridge for the selected grid points `175`
and `289`.  Because the exact reference spread is below `10^-15`, a supplied
rounded-output spread above `10^-15 + η` forces the rounded-error values at
these two points to differ by more than `η`. -/
theorem kahanRoundedGrid_175_289_error_spread_gt_of_output_spread
    (rounded : ℕ → ℝ) (η : ℝ)
    (hspread :
      (1 : ℝ) / 10 ^ 15 + η < |rounded 289 - rounded 175|) :
    η <
      |(rounded 289 - kahanRationalFunction (kahanHornerGridPoint 289)) -
        (rounded 175 - kahanRationalFunction (kahanHornerGridPoint 175))| := by
  set exactHi : ℝ := kahanRationalFunction (kahanHornerGridPoint 289)
  set exactLo : ℝ := kahanRationalFunction (kahanHornerGridPoint 175)
  set errDiff : ℝ := (rounded 289 - exactHi) - (rounded 175 - exactLo)
  have hexact :
      |exactHi - exactLo| < (1 : ℝ) / 10 ^ 15 := by
    simpa [exactHi, exactLo] using
      kahanRationalFunction_grid_175_289_variation_lt_one_e15
  have htri :
      |rounded 289 - rounded 175| ≤ |errDiff| + |exactHi - exactLo| := by
    calc
      |rounded 289 - rounded 175|
          = |errDiff + (exactHi - exactLo)| := by
              simp [errDiff]
              ring_nf
      _ ≤ |errDiff| + |exactHi - exactLo| := abs_add_le _ _
  by_contra hnot
  have herr : |errDiff| ≤ η := le_of_not_gt hnot
  have hle : |rounded 289 - rounded 175| ≤ η + (1 : ℝ) / 10 ^ 15 := by
    nlinarith
  nlinarith

/-- Selected-pair Figure 1.6 diagnostic bridge specialized to the modeled
IEEE-double finite round-to-even Horner path. -/
theorem ieeeDoubleKahanRationalFunction_175_289_error_spread_gt_of_output_spread
    (η : ℝ)
    (hspread :
      (1 : ℝ) / 10 ^ 15 + η <
        |ieeeDoubleKahanRationalFunction (kahanHornerGridPoint 289) -
          ieeeDoubleKahanRationalFunction (kahanHornerGridPoint 175)|) :
    η <
      |(ieeeDoubleKahanRationalFunction (kahanHornerGridPoint 289) -
          kahanRationalFunction (kahanHornerGridPoint 289)) -
        (ieeeDoubleKahanRationalFunction (kahanHornerGridPoint 175) -
          kahanRationalFunction (kahanHornerGridPoint 175))| := by
  exact
    kahanRoundedGrid_175_289_error_spread_gt_of_output_spread
      (fun j => ieeeDoubleKahanRationalFunction (kahanHornerGridPoint j))
      η hspread

/-- Stored IEEE-double version of the source grid point.  This makes the input
rounding in the plotted Horner path explicit instead of silently feeding the
exact real grid point to the first primitive operation. -/
noncomputable def ieeeDoubleKahanStoredGridPoint (k : ℕ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (kahanHornerGridPoint k)

/-- IEEE-double Horner path evaluated at the stored source-grid input. -/
noncomputable def ieeeDoubleKahanStoredGridRationalFunction (k : ℕ) : ℝ :=
  ieeeDoubleKahanRationalFunction (ieeeDoubleKahanStoredGridPoint k)

private theorem ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_one_adjacent
    {x a b : ℝ} {leftMantissa : ℕ}
    (hxnormal :
      FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange x)
    (hsliceLo :
      FloatingPointFormat.ieeeDoubleFormat.betaR ^ ((1 : ℤ) - 1) ≤ x)
    (hsliceHi : x ≤ FloatingPointFormat.ieeeDoubleFormat.betaR ^ (1 : ℤ))
    (hleftMantissa :
      FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa leftMantissa)
    (hrightMantissa :
      FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa
        (leftMantissa + 1))
    (hleft :
      a =
        FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
          leftMantissa (1 : ℤ))
    (hright :
      b =
        FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
          (leftMantissa + 1) (1 : ℤ))
    (ha_nonneg : 0 ≤ a)
    (hax : a ≤ x) (hxb : x ≤ b)
    (hcloser : |x - b| < |x - a|) :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven x = b := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hfinite :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hxnormal
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, leftMantissa, (1 : ℤ), hleftMantissa, hrightMantissa,
        Or.inl ?_⟩
    exact ⟨hleft, hright⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hnearest :
      FloatingPointFormat.nearestAdjacentRoundToEven x a b leftMantissa = b :=
    FloatingPointFormat.nearestAdjacentRoundToEven_eq_right_of_right_closer
      hcloser
  have hcert : fmt.sourceRoundToEvenEvidence x b := by
    refine Or.inl ?_
    refine ⟨(1 : ℤ), hsliceLo, hsliceHi, Or.inr ?_⟩
    refine
      ⟨a, b, leftMantissa, hadj, ?_, ha_nonneg, hax, hxb, hnearest.symm⟩
    exact ⟨false, (1 : ℤ), hleftMantissa, hleft⟩
  exact FloatingPointFormat.sourceRoundToEvenEvidence_unique hfinite hcert

/-- The selected `k=175` source grid point rounds upward to this IEEE-double
stored input. -/
theorem ieeeDoubleKahanStoredGridPoint_175_eq :
    ieeeDoubleKahanStoredGridPoint 175 =
      (7232781001557191 : ℝ) / 4503599627370496 := by
  unfold ieeeDoubleKahanStoredGridPoint
  apply
    ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_one_adjacent
      (a := (7232781001557190 : ℝ) / 4503599627370496)
      (leftMantissa := 7232781001557190)
  · apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [kahanHornerGridPoint]
    · norm_num [kahanHornerGridPoint]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.betaR, kahanHornerGridPoint]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.betaR, kahanHornerGridPoint]
  · norm_num [FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  · norm_num [FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  · norm_num [FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  · norm_num [FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  · norm_num
  · norm_num [kahanHornerGridPoint]
  · norm_num [kahanHornerGridPoint]
  · norm_num [kahanHornerGridPoint]

/-- The selected `k=289` source grid point rounds upward to this IEEE-double
stored input. -/
theorem ieeeDoubleKahanStoredGridPoint_289_eq :
    ieeeDoubleKahanStoredGridPoint 289 =
      (7232781001557305 : ℝ) / 4503599627370496 := by
  unfold ieeeDoubleKahanStoredGridPoint
  apply
    ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_one_adjacent
      (a := (7232781001557304 : ℝ) / 4503599627370496)
      (leftMantissa := 7232781001557304)
  · apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [kahanHornerGridPoint]
    · norm_num [kahanHornerGridPoint]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.betaR, kahanHornerGridPoint]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.betaR, kahanHornerGridPoint]
  · norm_num [FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  · norm_num [FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  · norm_num [FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  · norm_num [FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  · norm_num
  · norm_num [kahanHornerGridPoint]
  · norm_num [kahanHornerGridPoint]
  · norm_num [kahanHornerGridPoint]

/-- First numerator Horner primitive at the selected stored input `k=175`.
The product `4*xstored` is exactly representable in IEEE double. -/
theorem ieeeDoubleKahanStoredGridNumerator_m0_175_eq :
    ieeeDoubleKahanNumerator_m0 (ieeeDoubleKahanStoredGridPoint 175) =
      (7232781001557191 : ℝ) / 1125899906842624 := by
  rw [ieeeDoubleKahanStoredGridPoint_175_eq]
  unfold ieeeDoubleKahanNumerator_m0
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem]
  · norm_num [BasicOp.exact]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 7232781001557191, (3 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [BasicOp.exact, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]

/-- First numerator Horner primitive at the selected stored input `k=289`.
The product `4*xstored` is exactly representable in IEEE double. -/
theorem ieeeDoubleKahanStoredGridNumerator_m0_289_eq :
    ieeeDoubleKahanNumerator_m0 (ieeeDoubleKahanStoredGridPoint 289) =
      (7232781001557305 : ℝ) / 1125899906842624 := by
  rw [ieeeDoubleKahanStoredGridPoint_289_eq]
  unfold ieeeDoubleKahanNumerator_m0
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem]
  · norm_num [BasicOp.exact]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 7232781001557305, (3 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [BasicOp.exact, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]

/-- Second numerator Horner primitive at the selected stored input `k=175`.
The exact subtraction `59 - m0` lies closer to the left adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridNumerator_s0_175_eq :
    ieeeDoubleKahanNumerator_s0 (ieeeDoubleKahanStoredGridPoint 175) =
      (7399414187769703 : ℝ) / 140737488355328 := by
  unfold ieeeDoubleKahanNumerator_s0
  rw [ieeeDoubleKahanStoredGridNumerator_m0_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.sub 59
      ((7232781001557191 : ℝ) / 1125899906842624)
  let a : ℝ := (7399414187769703 : ℝ) / 140737488355328
  let b : ℝ := (7399414187769704 : ℝ) / 140737488355328
  have hm : fmt.normalizedMantissa 7399414187769703 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (7399414187769703 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, 7399414187769703, (6 : ℤ), hm, hmnext, Or.inl ?_⟩
    constructor
    · norm_num [fmt, a, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
    · norm_num [fmt, b, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hpolicy : fmt.sourceRoundToEvenEvidence exact (fmt.finiteRoundToEven exact) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hexactNormal
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hleftCloser : |exact - a| < |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.sub 59
          ((7232781001557191 : ℝ) / 1125899906842624)) =
      (7399414187769703 : ℝ) / 140737488355328
  simpa [fmt, exact, a] using hround

/-- Second numerator Horner primitive at the selected stored input `k=289`.
The exact subtraction `59 - m0` lies closer to the right adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridNumerator_s0_289_eq :
    ieeeDoubleKahanNumerator_s0 (ieeeDoubleKahanStoredGridPoint 289) =
      (7399414187769689 : ℝ) / 140737488355328 := by
  unfold ieeeDoubleKahanNumerator_s0
  rw [ieeeDoubleKahanStoredGridNumerator_m0_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.sub 59
      ((7232781001557305 : ℝ) / 1125899906842624)
  let a : ℝ := (7399414187769688 : ℝ) / 140737488355328
  let b : ℝ := (7399414187769689 : ℝ) / 140737488355328
  have hm : fmt.normalizedMantissa 7399414187769688 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (7399414187769688 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, 7399414187769688, (6 : ℤ), hm, hmnext, Or.inl ?_⟩
    constructor
    · norm_num [fmt, a, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
    · norm_num [fmt, b, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hpolicy : fmt.sourceRoundToEvenEvidence exact (fmt.finiteRoundToEven exact) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hexactNormal
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.sub 59
          ((7232781001557305 : ℝ) / 1125899906842624)) =
      (7399414187769689 : ℝ) / 140737488355328
  simpa [fmt, exact, b] using hround

/-- Third numerator Horner primitive at the selected stored input `k=175`.
The exact product `xstored*s0` lies closer to the right adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridNumerator_m1_175_eq :
    ieeeDoubleKahanNumerator_m1 (ieeeDoubleKahanStoredGridPoint 175) =
      (5941729592779215 : ℝ) / 70368744177664 := by
  unfold ieeeDoubleKahanNumerator_m1
  rw [ieeeDoubleKahanStoredGridNumerator_s0_175_eq]
  rw [ieeeDoubleKahanStoredGridPoint_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557191 : ℝ) / 4503599627370496)
      ((7399414187769703 : ℝ) / 140737488355328)
  let a : ℝ := (5941729592779214 : ℝ) / 70368744177664
  let b : ℝ := (5941729592779215 : ℝ) / 70368744177664
  have hm : fmt.normalizedMantissa 5941729592779214 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (5941729592779214 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, 5941729592779214, (7 : ℤ), hm, hmnext, Or.inl ?_⟩
    constructor
    · norm_num [fmt, a, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
    · norm_num [fmt, b, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hpolicy : fmt.sourceRoundToEvenEvidence exact (fmt.finiteRoundToEven exact) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hexactNormal
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557191 : ℝ) / 4503599627370496)
          ((7399414187769703 : ℝ) / 140737488355328)) =
      (5941729592779215 : ℝ) / 70368744177664
  simpa [fmt, exact, b] using hround

/-- Third numerator Horner primitive at the selected stored input `k=289`.
The exact product `xstored*s0` lies closer to the left adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridNumerator_m1_289_eq :
    ieeeDoubleKahanNumerator_m1 (ieeeDoubleKahanStoredGridPoint 289) =
      (5941729592779297 : ℝ) / 70368744177664 := by
  unfold ieeeDoubleKahanNumerator_m1
  rw [ieeeDoubleKahanStoredGridNumerator_s0_289_eq]
  rw [ieeeDoubleKahanStoredGridPoint_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557305 : ℝ) / 4503599627370496)
      ((7399414187769689 : ℝ) / 140737488355328)
  let a : ℝ := (5941729592779297 : ℝ) / 70368744177664
  let b : ℝ := (5941729592779298 : ℝ) / 70368744177664
  have hm : fmt.normalizedMantissa 5941729592779297 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (5941729592779297 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, 5941729592779297, (7 : ℤ), hm, hmnext, Or.inl ?_⟩
    constructor
    · norm_num [fmt, a, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
    · norm_num [fmt, b, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hpolicy : fmt.sourceRoundToEvenEvidence exact (fmt.finiteRoundToEven exact) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hexactNormal
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hleftCloser : |exact - a| < |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557305 : ℝ) / 4503599627370496)
          ((7399414187769689 : ℝ) / 140737488355328)) =
      (5941729592779297 : ℝ) / 70368744177664
  simpa [fmt, exact, a] using hround

/-- Fourth numerator Horner primitive at the selected stored input `k=175`.
The exact subtraction `324 - m1` is exactly halfway between adjacent
IEEE-double endpoints, and the left mantissa is even. -/
theorem ieeeDoubleKahanStoredGridNumerator_s1_175_eq :
    ieeeDoubleKahanNumerator_s1 (ieeeDoubleKahanStoredGridPoint 175) =
      (8428871760391960 : ℝ) / 35184372088832 := by
  unfold ieeeDoubleKahanNumerator_s1
  rw [ieeeDoubleKahanStoredGridNumerator_m1_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.sub 324
      ((5941729592779215 : ℝ) / 70368744177664)
  let a : ℝ := (8428871760391960 : ℝ) / 35184372088832
  let b : ℝ := (8428871760391961 : ℝ) / 35184372088832
  have hm : fmt.normalizedMantissa 8428871760391960 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (8428871760391960 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 8428871760391960 (8 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (8428871760391960 + 1) (8 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, 8428871760391960, (8 : ℤ), hm, hmnext, Or.inl ?_⟩
    exact ⟨hleft, hright⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hpolicy : fmt.sourceRoundToEvenEvidence exact (fmt.finiteRoundToEven exact) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hexactNormal
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have htie : |exact - a| = |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have heven : FloatingPointFormat.evenMantissa 8428871760391960 := by
    norm_num [FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven exact = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
      hpolicy hadj hstrict hm hleft htie heven
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.sub 324
          ((5941729592779215 : ℝ) / 70368744177664)) =
      (8428871760391960 : ℝ) / 35184372088832
  simpa [fmt, exact, a] using hround

/-- Fourth numerator Horner primitive at the selected stored input `k=289`.
The exact subtraction `324 - m1` is exactly halfway between adjacent
IEEE-double endpoints, and the left mantissa is odd, so the right endpoint is
chosen. -/
theorem ieeeDoubleKahanStoredGridNumerator_s1_289_eq :
    ieeeDoubleKahanNumerator_s1 (ieeeDoubleKahanStoredGridPoint 289) =
      (8428871760391920 : ℝ) / 35184372088832 := by
  unfold ieeeDoubleKahanNumerator_s1
  rw [ieeeDoubleKahanStoredGridNumerator_m1_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.sub 324
      ((5941729592779297 : ℝ) / 70368744177664)
  let a : ℝ := (8428871760391919 : ℝ) / 35184372088832
  let b : ℝ := (8428871760391920 : ℝ) / 35184372088832
  have hm : fmt.normalizedMantissa 8428871760391919 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (8428871760391919 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 8428871760391919 (8 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (8428871760391919 + 1) (8 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, 8428871760391919, (8 : ℤ), hm, hmnext, Or.inl ?_⟩
    exact ⟨hleft, hright⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hpolicy : fmt.sourceRoundToEvenEvidence exact (fmt.finiteRoundToEven exact) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hexactNormal
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have htie : |exact - a| = |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hodd : ¬ FloatingPointFormat.evenMantissa 8428871760391919 := by
    norm_num [FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven exact = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hm hleft htie hodd
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.sub 324
          ((5941729592779297 : ℝ) / 70368744177664)) =
      (8428871760391920 : ℝ) / 35184372088832
  simpa [fmt, exact, b] using hround

/-- Fifth numerator Horner primitive at the selected stored input `k=175`.
The exact product `xstored*s1` lies closer to the left adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridNumerator_m2_175_eq :
    ieeeDoubleKahanNumerator_m2 (ieeeDoubleKahanStoredGridPoint 175) =
      (6768384023594907 : ℝ) / 17592186044416 := by
  unfold ieeeDoubleKahanNumerator_m2
  rw [ieeeDoubleKahanStoredGridNumerator_s1_175_eq]
  rw [ieeeDoubleKahanStoredGridPoint_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557191 : ℝ) / 4503599627370496)
      ((8428871760391960 : ℝ) / 35184372088832)
  let a : ℝ := (6768384023594907 : ℝ) / 17592186044416
  let b : ℝ := (6768384023594908 : ℝ) / 17592186044416
  have hm : fmt.normalizedMantissa 6768384023594907 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (6768384023594907 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, 6768384023594907, (9 : ℤ), hm, hmnext, Or.inl ?_⟩
    constructor
    · norm_num [fmt, a, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
    · norm_num [fmt, b, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hpolicy : fmt.sourceRoundToEvenEvidence exact (fmt.finiteRoundToEven exact) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hexactNormal
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hleftCloser : |exact - a| < |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557191 : ℝ) / 4503599627370496)
          ((8428871760391960 : ℝ) / 35184372088832)) =
      (6768384023594907 : ℝ) / 17592186044416
  simpa [fmt, exact, a] using hround

/-- Fifth numerator Horner primitive at the selected stored input `k=289`.
The exact product `xstored*s1` lies closer to the right adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridNumerator_m2_289_eq :
    ieeeDoubleKahanNumerator_m2 (ieeeDoubleKahanStoredGridPoint 289) =
      (6768384023594982 : ℝ) / 17592186044416 := by
  unfold ieeeDoubleKahanNumerator_m2
  rw [ieeeDoubleKahanStoredGridNumerator_s1_289_eq]
  rw [ieeeDoubleKahanStoredGridPoint_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557305 : ℝ) / 4503599627370496)
      ((8428871760391920 : ℝ) / 35184372088832)
  let a : ℝ := (6768384023594981 : ℝ) / 17592186044416
  let b : ℝ := (6768384023594982 : ℝ) / 17592186044416
  have hm : fmt.normalizedMantissa 6768384023594981 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (6768384023594981 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, 6768384023594981, (9 : ℤ), hm, hmnext, Or.inl ?_⟩
    constructor
    · norm_num [fmt, a, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
    · norm_num [fmt, b, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hpolicy : fmt.sourceRoundToEvenEvidence exact (fmt.finiteRoundToEven exact) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hexactNormal
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557305 : ℝ) / 4503599627370496)
          ((8428871760391920 : ℝ) / 35184372088832)) =
      (6768384023594982 : ℝ) / 17592186044416
  simpa [fmt, exact, b] using hround

/-- Sixth numerator Horner primitive at the selected stored input `k=175`.
The subtraction `751 - m2` is exactly representable in IEEE double. -/
theorem ieeeDoubleKahanStoredGridNumerator_s2_175_eq :
    ieeeDoubleKahanNumerator_s2 (ieeeDoubleKahanStoredGridPoint 175) =
      (6443347695761509 : ℝ) / 17592186044416 := by
  unfold ieeeDoubleKahanNumerator_s2
  rw [ieeeDoubleKahanStoredGridNumerator_m2_175_eq]
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem]
  · norm_num [BasicOp.exact]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 6443347695761509, (9 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [BasicOp.exact, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]

/-- Sixth numerator Horner primitive at the selected stored input `k=289`.
The subtraction `751 - m2` is exactly representable in IEEE double. -/
theorem ieeeDoubleKahanStoredGridNumerator_s2_289_eq :
    ieeeDoubleKahanNumerator_s2 (ieeeDoubleKahanStoredGridPoint 289) =
      (6443347695761434 : ℝ) / 17592186044416 := by
  unfold ieeeDoubleKahanNumerator_s2
  rw [ieeeDoubleKahanStoredGridNumerator_m2_289_eq]
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem]
  · norm_num [BasicOp.exact]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 6443347695761434, (9 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [BasicOp.exact, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]

/-- Seventh numerator Horner primitive at the selected stored input `k=175`.
The exact product `xstored*s2` lies closer to the right adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridNumerator_m3_175_eq :
    ieeeDoubleKahanNumerator_m3 (ieeeDoubleKahanStoredGridPoint 175) =
      (5174008199696617 : ℝ) / 8796093022208 := by
  unfold ieeeDoubleKahanNumerator_m3
  rw [ieeeDoubleKahanStoredGridNumerator_s2_175_eq]
  rw [ieeeDoubleKahanStoredGridPoint_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557191 : ℝ) / 4503599627370496)
      ((6443347695761509 : ℝ) / 17592186044416)
  let a : ℝ := (5174008199696616 : ℝ) / 8796093022208
  let b : ℝ := (5174008199696617 : ℝ) / 8796093022208
  have hm : fmt.normalizedMantissa 5174008199696616 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (5174008199696616 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, 5174008199696616, (10 : ℤ), hm, hmnext, Or.inl ?_⟩
    constructor
    · norm_num [fmt, a, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
    · norm_num [fmt, b, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hpolicy : fmt.sourceRoundToEvenEvidence exact (fmt.finiteRoundToEven exact) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hexactNormal
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557191 : ℝ) / 4503599627370496)
          ((6443347695761509 : ℝ) / 17592186044416)) =
      (5174008199696617 : ℝ) / 8796093022208
  simpa [fmt, exact, b] using hround

/-- Seventh numerator Horner primitive at the selected stored input `k=289`.
The exact product `xstored*s2` lies closer to the right adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridNumerator_m3_289_eq :
    ieeeDoubleKahanNumerator_m3 (ieeeDoubleKahanStoredGridPoint 289) =
      (5174008199696638 : ℝ) / 8796093022208 := by
  unfold ieeeDoubleKahanNumerator_m3
  rw [ieeeDoubleKahanStoredGridNumerator_s2_289_eq]
  rw [ieeeDoubleKahanStoredGridPoint_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557305 : ℝ) / 4503599627370496)
      ((6443347695761434 : ℝ) / 17592186044416)
  let a : ℝ := (5174008199696637 : ℝ) / 8796093022208
  let b : ℝ := (5174008199696638 : ℝ) / 8796093022208
  have hm : fmt.normalizedMantissa 5174008199696637 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (5174008199696637 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, 5174008199696637, (10 : ℤ), hm, hmnext, Or.inl ?_⟩
    constructor
    · norm_num [fmt, a, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
    · norm_num [fmt, b, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hpolicy : fmt.sourceRoundToEvenEvidence exact (fmt.finiteRoundToEven exact) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hexactNormal
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557305 : ℝ) / 4503599627370496)
          ((6443347695761434 : ℝ) / 17592186044416)) =
      (5174008199696638 : ℝ) / 8796093022208
  simpa [fmt, exact, b] using hround

/-- Final rounded numerator Horner value at the selected stored input `k=175`.
The subtraction `622 - m3` is exactly representable in IEEE double. -/
theorem ieeeDoubleKahanStoredGridHornerNumerator_175_eq :
    ieeeDoubleKahanHornerNumerator (ieeeDoubleKahanStoredGridPoint 175) =
      (4754586561868144 : ℝ) / 140737488355328 := by
  unfold ieeeDoubleKahanHornerNumerator
  rw [ieeeDoubleKahanStoredGridNumerator_m3_175_eq]
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem]
  · norm_num [BasicOp.exact]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 4754586561868144, (6 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [BasicOp.exact, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]

/-- Final rounded numerator Horner value at the selected stored input `k=289`.
The subtraction `622 - m3` is exactly representable in IEEE double. -/
theorem ieeeDoubleKahanStoredGridHornerNumerator_289_eq :
    ieeeDoubleKahanHornerNumerator (ieeeDoubleKahanStoredGridPoint 289) =
      (4754586561867808 : ℝ) / 140737488355328 := by
  unfold ieeeDoubleKahanHornerNumerator
  rw [ieeeDoubleKahanStoredGridNumerator_m3_289_eq]
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem]
  · norm_num [BasicOp.exact]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 4754586561867808, (6 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [BasicOp.exact, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]

private theorem ieeeDouble_finiteRoundToEven_eq_left_of_pos_same_exp_adjacent
    {x a b : ℝ} {leftMantissa : ℕ} {e : ℤ}
    (hxnormal :
      FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange x)
    (hleftMantissa :
      FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa leftMantissa)
    (hrightMantissa :
      FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa
        (leftMantissa + 1))
    (hleft :
      a =
        FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
          leftMantissa e)
    (hright :
      b =
        FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
          (leftMantissa + 1) e)
    (hstrict : a < x ∧ x < b)
    (hcloser : |x - a| < |x - b|) :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven x = a := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hxnormal
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, leftMantissa, e, hleftMantissa, hrightMantissa, Or.inl ?_⟩
    exact ⟨hleft, hright⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  exact
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hcloser

private theorem ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_adjacent
    {x a b : ℝ} {leftMantissa : ℕ} {e : ℤ}
    (hxnormal :
      FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange x)
    (hleftMantissa :
      FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa leftMantissa)
    (hrightMantissa :
      FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa
        (leftMantissa + 1))
    (hleft :
      a =
        FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
          leftMantissa e)
    (hright :
      b =
        FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
          (leftMantissa + 1) e)
    (hstrict : a < x ∧ x < b)
    (hcloser : |x - b| < |x - a|) :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven x = b := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hxnormal
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, leftMantissa, e, hleftMantissa, hrightMantissa, Or.inl ?_⟩
    exact ⟨hleft, hright⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  exact
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hcloser

private theorem ieeeDouble_finiteRoundToEven_eq_left_of_pos_same_exp_tie_even
    {x a b : ℝ} {leftMantissa : ℕ} {e : ℤ}
    (hxnormal :
      FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange x)
    (hleftMantissa :
      FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa leftMantissa)
    (hrightMantissa :
      FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa
        (leftMantissa + 1))
    (hleft :
      a =
        FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
          leftMantissa e)
    (hright :
      b =
        FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
          (leftMantissa + 1) e)
    (hstrict : a < x ∧ x < b)
    (htie : |x - a| = |x - b|)
    (heven : FloatingPointFormat.evenMantissa leftMantissa) :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven x = a := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hxnormal
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, leftMantissa, e, hleftMantissa, hrightMantissa, Or.inl ?_⟩
    exact ⟨hleft, hright⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  exact
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
      hpolicy hadj hstrict hleftMantissa hleft htie heven

private theorem ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_tie_odd
    {x a b : ℝ} {leftMantissa : ℕ} {e : ℤ}
    (hxnormal :
      FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange x)
    (hleftMantissa :
      FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa leftMantissa)
    (hrightMantissa :
      FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa
        (leftMantissa + 1))
    (hleft :
      a =
        FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
          leftMantissa e)
    (hright :
      b =
        FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
          (leftMantissa + 1) e)
    (hstrict : a < x ∧ x < b)
    (htie : |x - a| = |x - b|)
    (hodd : ¬ FloatingPointFormat.evenMantissa leftMantissa) :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven x = b := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hxnormal
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, leftMantissa, e, hleftMantissa, hrightMantissa, Or.inl ?_⟩
    exact ⟨hleft, hright⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  exact
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hleftMantissa hleft htie hodd

/-- First denominator Horner primitive at the selected stored input `k=175`.
The exact subtraction `14 - xstored` lies closer to the left adjacent
IEEE-double endpoint. -/
theorem ieeeDoubleKahanStoredGridDenominator_s0_175_eq :
    ieeeDoubleKahanDenominator_s0 (ieeeDoubleKahanStoredGridPoint 175) =
      (6977201722703719 : ℝ) / 562949953421312 := by
  unfold ieeeDoubleKahanDenominator_s0
  rw [ieeeDoubleKahanStoredGridPoint_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.sub 14
      ((7232781001557191 : ℝ) / 4503599627370496)
  let a : ℝ := (6977201722703719 : ℝ) / 562949953421312
  let b : ℝ := (6977201722703720 : ℝ) / 562949953421312
  have hm : fmt.normalizedMantissa 6977201722703719 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (6977201722703719 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 6977201722703719 (4 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (6977201722703719 + 1) (4 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hleftCloser : |exact - a| < |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = a :=
    ieeeDouble_finiteRoundToEven_eq_left_of_pos_same_exp_adjacent
      hexactNormal hm hmnext hleft hright hstrict hleftCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.sub 14
          ((7232781001557191 : ℝ) / 4503599627370496)) =
      (6977201722703719 : ℝ) / 562949953421312
  simpa [fmt, exact, a] using hround

/-- First denominator Horner primitive at the selected stored input `k=289`.
The exact subtraction `14 - xstored` lies closer to the right adjacent
IEEE-double endpoint. -/
theorem ieeeDoubleKahanStoredGridDenominator_s0_289_eq :
    ieeeDoubleKahanDenominator_s0 (ieeeDoubleKahanStoredGridPoint 289) =
      (6977201722703705 : ℝ) / 562949953421312 := by
  unfold ieeeDoubleKahanDenominator_s0
  rw [ieeeDoubleKahanStoredGridPoint_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.sub 14
      ((7232781001557305 : ℝ) / 4503599627370496)
  let a : ℝ := (6977201722703704 : ℝ) / 562949953421312
  let b : ℝ := (6977201722703705 : ℝ) / 562949953421312
  have hm : fmt.normalizedMantissa 6977201722703704 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (6977201722703704 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 6977201722703704 (4 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (6977201722703704 + 1) (4 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_adjacent
      hexactNormal hm hmnext hleft hright hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.sub 14
          ((7232781001557305 : ℝ) / 4503599627370496)) =
      (6977201722703705 : ℝ) / 562949953421312
  simpa [fmt, exact, b] using hround

/-- Second denominator Horner primitive at the selected stored input `k=175`.
The exact product `xstored*s0` lies closer to the left adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridDenominator_m1_175_eq :
    ieeeDoubleKahanDenominator_m1 (ieeeDoubleKahanStoredGridPoint 175) =
      (5602692983331221 : ℝ) / 281474976710656 := by
  unfold ieeeDoubleKahanDenominator_m1
  rw [ieeeDoubleKahanStoredGridDenominator_s0_175_eq]
  rw [ieeeDoubleKahanStoredGridPoint_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557191 : ℝ) / 4503599627370496)
      ((6977201722703719 : ℝ) / 562949953421312)
  let a : ℝ := (5602692983331221 : ℝ) / 281474976710656
  let b : ℝ := (5602692983331222 : ℝ) / 281474976710656
  have hm : fmt.normalizedMantissa 5602692983331221 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (5602692983331221 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 5602692983331221 (5 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (5602692983331221 + 1) (5 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hleftCloser : |exact - a| < |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = a :=
    ieeeDouble_finiteRoundToEven_eq_left_of_pos_same_exp_adjacent
      hexactNormal hm hmnext hleft hright hstrict hleftCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557191 : ℝ) / 4503599627370496)
          ((6977201722703719 : ℝ) / 562949953421312)) =
      (5602692983331221 : ℝ) / 281474976710656
  simpa [fmt, exact, a] using hround

/-- Second denominator Horner primitive at the selected stored input `k=289`.
The exact product `xstored*s0` lies closer to the right adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridDenominator_m1_289_eq :
    ieeeDoubleKahanDenominator_m1 (ieeeDoubleKahanStoredGridPoint 289) =
      (5602692983331299 : ℝ) / 281474976710656 := by
  unfold ieeeDoubleKahanDenominator_m1
  rw [ieeeDoubleKahanStoredGridDenominator_s0_289_eq]
  rw [ieeeDoubleKahanStoredGridPoint_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557305 : ℝ) / 4503599627370496)
      ((6977201722703705 : ℝ) / 562949953421312)
  let a : ℝ := (5602692983331298 : ℝ) / 281474976710656
  let b : ℝ := (5602692983331299 : ℝ) / 281474976710656
  have hm : fmt.normalizedMantissa 5602692983331298 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (5602692983331298 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 5602692983331298 (5 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (5602692983331298 + 1) (5 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_adjacent
      hexactNormal hm hmnext hleft hright hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557305 : ℝ) / 4503599627370496)
          ((6977201722703705 : ℝ) / 562949953421312)) =
      (5602692983331299 : ℝ) / 281474976710656
  simpa [fmt, exact, b] using hround

/-- Third denominator Horner primitive at the selected stored input `k=175`.
The exact subtraction `72 - m1` is a midpoint case and rounds to the even
right endpoint. -/
theorem ieeeDoubleKahanStoredGridDenominator_s1_175_eq :
    ieeeDoubleKahanDenominator_s1 (ieeeDoubleKahanStoredGridPoint 175) =
      (7331752669918006 : ℝ) / 140737488355328 := by
  unfold ieeeDoubleKahanDenominator_s1
  rw [ieeeDoubleKahanStoredGridDenominator_m1_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.sub 72
      ((5602692983331221 : ℝ) / 281474976710656)
  let a : ℝ := (7331752669918005 : ℝ) / 140737488355328
  let b : ℝ := (7331752669918006 : ℝ) / 140737488355328
  have hm : fmt.normalizedMantissa 7331752669918005 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (7331752669918005 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 7331752669918005 (6 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (7331752669918005 + 1) (6 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have htie : |exact - a| = |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hodd : ¬ FloatingPointFormat.evenMantissa 7331752669918005 := by
    norm_num [FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven exact = b :=
    ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_tie_odd
      hexactNormal hm hmnext hleft hright hstrict htie hodd
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.sub 72
          ((5602692983331221 : ℝ) / 281474976710656)) =
      (7331752669918006 : ℝ) / 140737488355328
  simpa [fmt, exact, b] using hround

/-- Third denominator Horner primitive at the selected stored input `k=289`.
The exact subtraction `72 - m1` is a midpoint case and rounds to the even left
endpoint. -/
theorem ieeeDoubleKahanStoredGridDenominator_s1_289_eq :
    ieeeDoubleKahanDenominator_s1 (ieeeDoubleKahanStoredGridPoint 289) =
      (7331752669917966 : ℝ) / 140737488355328 := by
  unfold ieeeDoubleKahanDenominator_s1
  rw [ieeeDoubleKahanStoredGridDenominator_m1_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.sub 72
      ((5602692983331299 : ℝ) / 281474976710656)
  let a : ℝ := (7331752669917966 : ℝ) / 140737488355328
  let b : ℝ := (7331752669917967 : ℝ) / 140737488355328
  have hm : fmt.normalizedMantissa 7331752669917966 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (7331752669917966 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 7331752669917966 (6 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (7331752669917966 + 1) (6 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have htie : |exact - a| = |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have heven : FloatingPointFormat.evenMantissa 7331752669917966 := by
    norm_num [FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven exact = a :=
    ieeeDouble_finiteRoundToEven_eq_left_of_pos_same_exp_tie_even
      hexactNormal hm hmnext hleft hright hstrict htie heven
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.sub 72
          ((5602692983331299 : ℝ) / 281474976710656)) =
      (7331752669917966 : ℝ) / 140737488355328
  simpa [fmt, exact, a] using hround

/-- Fourth denominator Horner primitive at the selected stored input `k=175`.
The exact product `xstored*s1` lies closer to the right adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridDenominator_m2_175_eq :
    ieeeDoubleKahanDenominator_m2 (ieeeDoubleKahanStoredGridPoint 175) =
      (5887397393944301 : ℝ) / 70368744177664 := by
  unfold ieeeDoubleKahanDenominator_m2
  rw [ieeeDoubleKahanStoredGridDenominator_s1_175_eq]
  rw [ieeeDoubleKahanStoredGridPoint_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557191 : ℝ) / 4503599627370496)
      ((7331752669918006 : ℝ) / 140737488355328)
  let a : ℝ := (5887397393944300 : ℝ) / 70368744177664
  let b : ℝ := (5887397393944301 : ℝ) / 70368744177664
  have hm : fmt.normalizedMantissa 5887397393944300 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (5887397393944300 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 5887397393944300 (7 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (5887397393944300 + 1) (7 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_adjacent
      hexactNormal hm hmnext hleft hright hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557191 : ℝ) / 4503599627370496)
          ((7331752669918006 : ℝ) / 140737488355328)) =
      (5887397393944301 : ℝ) / 70368744177664
  simpa [fmt, exact, b] using hround

/-- Fourth denominator Horner primitive at the selected stored input `k=289`.
The exact product `xstored*s1` lies closer to the left adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridDenominator_m2_289_eq :
    ieeeDoubleKahanDenominator_m2 (ieeeDoubleKahanStoredGridPoint 289) =
      (5887397393944361 : ℝ) / 70368744177664 := by
  unfold ieeeDoubleKahanDenominator_m2
  rw [ieeeDoubleKahanStoredGridDenominator_s1_289_eq]
  rw [ieeeDoubleKahanStoredGridPoint_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557305 : ℝ) / 4503599627370496)
      ((7331752669917966 : ℝ) / 140737488355328)
  let a : ℝ := (5887397393944361 : ℝ) / 70368744177664
  let b : ℝ := (5887397393944362 : ℝ) / 70368744177664
  have hm : fmt.normalizedMantissa 5887397393944361 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (5887397393944361 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 5887397393944361 (7 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (5887397393944361 + 1) (7 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hleftCloser : |exact - a| < |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = a :=
    ieeeDouble_finiteRoundToEven_eq_left_of_pos_same_exp_adjacent
      hexactNormal hm hmnext hleft hright hstrict hleftCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557305 : ℝ) / 4503599627370496)
          ((7331752669917966 : ℝ) / 140737488355328)) =
      (5887397393944361 : ℝ) / 70368744177664
  simpa [fmt, exact, a] using hround

/-- Fifth denominator Horner primitive at the selected stored input `k=175`.
The subtraction `151 - m2` is exactly representable in IEEE double. -/
theorem ieeeDoubleKahanStoredGridDenominator_s2_175_eq :
    ieeeDoubleKahanDenominator_s2 (ieeeDoubleKahanStoredGridPoint 175) =
      (4738282976882963 : ℝ) / 70368744177664 := by
  unfold ieeeDoubleKahanDenominator_s2
  rw [ieeeDoubleKahanStoredGridDenominator_m2_175_eq]
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem]
  · norm_num [BasicOp.exact]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 4738282976882963, (7 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [BasicOp.exact, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]

/-- Fifth denominator Horner primitive at the selected stored input `k=289`.
The subtraction `151 - m2` is exactly representable in IEEE double. -/
theorem ieeeDoubleKahanStoredGridDenominator_s2_289_eq :
    ieeeDoubleKahanDenominator_s2 (ieeeDoubleKahanStoredGridPoint 289) =
      (4738282976882903 : ℝ) / 70368744177664 := by
  unfold ieeeDoubleKahanDenominator_s2
  rw [ieeeDoubleKahanStoredGridDenominator_m2_289_eq]
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem]
  · norm_num [BasicOp.exact]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 4738282976882903, (7 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [BasicOp.exact, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]

/-- Sixth denominator Horner primitive at the selected stored input `k=175`.
The exact product `xstored*s2` lies closer to the left adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridDenominator_m3_175_eq :
    ieeeDoubleKahanDenominator_m3 (ieeeDoubleKahanStoredGridPoint 175) =
      (7609682460874222 : ℝ) / 70368744177664 := by
  unfold ieeeDoubleKahanDenominator_m3
  rw [ieeeDoubleKahanStoredGridDenominator_s2_175_eq]
  rw [ieeeDoubleKahanStoredGridPoint_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557191 : ℝ) / 4503599627370496)
      ((4738282976882963 : ℝ) / 70368744177664)
  let a : ℝ := (7609682460874222 : ℝ) / 70368744177664
  let b : ℝ := (7609682460874223 : ℝ) / 70368744177664
  have hm : fmt.normalizedMantissa 7609682460874222 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (7609682460874222 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 7609682460874222 (7 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (7609682460874222 + 1) (7 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hleftCloser : |exact - a| < |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = a :=
    ieeeDouble_finiteRoundToEven_eq_left_of_pos_same_exp_adjacent
      hexactNormal hm hmnext hleft hright hstrict hleftCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557191 : ℝ) / 4503599627370496)
          ((4738282976882963 : ℝ) / 70368744177664)) =
      (7609682460874222 : ℝ) / 70368744177664
  simpa [fmt, exact, a] using hround

/-- Sixth denominator Horner primitive at the selected stored input `k=289`.
The exact product `xstored*s2` lies closer to the right adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridDenominator_m3_289_eq :
    ieeeDoubleKahanDenominator_m3 (ieeeDoubleKahanStoredGridPoint 289) =
      (7609682460874246 : ℝ) / 70368744177664 := by
  unfold ieeeDoubleKahanDenominator_m3
  rw [ieeeDoubleKahanStoredGridDenominator_s2_289_eq]
  rw [ieeeDoubleKahanStoredGridPoint_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557305 : ℝ) / 4503599627370496)
      ((4738282976882903 : ℝ) / 70368744177664)
  let a : ℝ := (7609682460874245 : ℝ) / 70368744177664
  let b : ℝ := (7609682460874246 : ℝ) / 70368744177664
  have hm : fmt.normalizedMantissa 7609682460874245 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (7609682460874245 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 7609682460874245 (7 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (7609682460874245 + 1) (7 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_adjacent
      hexactNormal hm hmnext hleft hright hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557305 : ℝ) / 4503599627370496)
          ((4738282976882903 : ℝ) / 70368744177664)) =
      (7609682460874246 : ℝ) / 70368744177664
  simpa [fmt, exact, b] using hround

/-- Final rounded denominator Horner value at the selected stored input
`k=175`. The subtraction `112 - m3` is exactly representable in IEEE double. -/
theorem ieeeDoubleKahanStoredGridHornerDenominator_175_eq :
    ieeeDoubleKahanHornerDenominator (ieeeDoubleKahanStoredGridPoint 175) =
      (135808443512073 : ℝ) / 35184372088832 := by
  unfold ieeeDoubleKahanHornerDenominator
  rw [ieeeDoubleKahanStoredGridDenominator_m3_175_eq]
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem]
  · norm_num [BasicOp.exact]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 8691740384772672, (2 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [BasicOp.exact, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]

/-- Final rounded denominator Horner value at the selected stored input
`k=289`. The subtraction `112 - m3` is exactly representable in IEEE double. -/
theorem ieeeDoubleKahanStoredGridHornerDenominator_289_eq :
    ieeeDoubleKahanHornerDenominator (ieeeDoubleKahanStoredGridPoint 289) =
      (135808443512061 : ℝ) / 35184372088832 := by
  unfold ieeeDoubleKahanHornerDenominator
  rw [ieeeDoubleKahanStoredGridDenominator_m3_289_eq]
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem]
  · norm_num [BasicOp.exact]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 8691740384771904, (2 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [BasicOp.exact, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]

/-- Final stored-input IEEE-double Horner quotient at selected input `k=175`. -/
theorem ieeeDoubleKahanStoredGridRationalFunction_175_eq :
    ieeeDoubleKahanStoredGridRationalFunction 175 =
      (4927149988474991 : ℝ) / 562949953421312 := by
  unfold ieeeDoubleKahanStoredGridRationalFunction
  unfold ieeeDoubleKahanRationalFunction
  rw [ieeeDoubleKahanStoredGridHornerNumerator_175_eq]
  rw [ieeeDoubleKahanStoredGridHornerDenominator_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.div
      ((4754586561868144 : ℝ) / 140737488355328)
      ((135808443512073 : ℝ) / 35184372088832)
  let a : ℝ := (4927149988474990 : ℝ) / 562949953421312
  let b : ℝ := (4927149988474991 : ℝ) / 562949953421312
  have hm : fmt.normalizedMantissa 4927149988474990 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (4927149988474990 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 4927149988474990 (4 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (4927149988474990 + 1) (4 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_adjacent
      hexactNormal hm hmnext hleft hright hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.div
          ((4754586561868144 : ℝ) / 140737488355328)
          ((135808443512073 : ℝ) / 35184372088832)) =
      (4927149988474991 : ℝ) / 562949953421312
  simpa [fmt, exact, b] using hround

/-- Final stored-input IEEE-double Horner quotient at selected input `k=289`. -/
theorem ieeeDoubleKahanStoredGridRationalFunction_289_eq :
    ieeeDoubleKahanStoredGridRationalFunction 289 =
      (2463574994237539 : ℝ) / 281474976710656 := by
  unfold ieeeDoubleKahanStoredGridRationalFunction
  unfold ieeeDoubleKahanRationalFunction
  rw [ieeeDoubleKahanStoredGridHornerNumerator_289_eq]
  rw [ieeeDoubleKahanStoredGridHornerDenominator_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.div
      ((4754586561867808 : ℝ) / 140737488355328)
      ((135808443512061 : ℝ) / 35184372088832)
  let a : ℝ := (4927149988475077 : ℝ) / 562949953421312
  let b : ℝ := (4927149988475078 : ℝ) / 562949953421312
  have hm : fmt.normalizedMantissa 4927149988475077 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (4927149988475077 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 4927149988475077 (4 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (4927149988475077 + 1) (4 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_adjacent
      hexactNormal hm hmnext hleft hright hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.div
          ((4754586561867808 : ℝ) / 140737488355328)
          ((135808443512061 : ℝ) / 35184372088832)) =
      (2463574994237539 : ℝ) / 281474976710656
  have hb : b = (2463574994237539 : ℝ) / 281474976710656 := by
    norm_num [b]
  rw [← hb]
  simpa [fmt, exact] using hround

/-- Selected-pair Figure 1.6 diagnostic bridge specialized to the modeled
IEEE-double Horner path with the source-grid input first stored in IEEE double. -/
theorem ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_of_output_spread
    (η : ℝ)
    (hspread :
      (1 : ℝ) / 10 ^ 15 + η <
        |ieeeDoubleKahanStoredGridRationalFunction 289 -
          ieeeDoubleKahanStoredGridRationalFunction 175|) :
    η <
      |(ieeeDoubleKahanStoredGridRationalFunction 289 -
          kahanRationalFunction (kahanHornerGridPoint 289)) -
        (ieeeDoubleKahanStoredGridRationalFunction 175 -
          kahanRationalFunction (kahanHornerGridPoint 175))| := by
  exact
    kahanRoundedGrid_175_289_error_spread_gt_of_output_spread
      ieeeDoubleKahanStoredGridRationalFunction η hspread

/-- Reusable bridge from two selected stored-grid IEEE-double rounded Horner
values to the Figure 1.6 error spread lower bound.  The unconditional theorem
below supplies the two exact stored input/output certificates. -/
theorem ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_one_e13_of_output_values
    (h175 :
      ieeeDoubleKahanStoredGridRationalFunction 175 =
        (4927149988474991 : ℝ) / 562949953421312)
    (h289 :
      ieeeDoubleKahanStoredGridRationalFunction 289 =
        (2463574994237539 : ℝ) / 281474976710656) :
    (1 : ℝ) / 10 ^ 13 <
      |(ieeeDoubleKahanStoredGridRationalFunction 289 -
          kahanRationalFunction (kahanHornerGridPoint 289)) -
        (ieeeDoubleKahanStoredGridRationalFunction 175 -
          kahanRationalFunction (kahanHornerGridPoint 175))| := by
  apply ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_of_output_spread
    (η := (1 : ℝ) / 10 ^ 13)
  rw [h289, h175]
  norm_num

/-- Fully certified selected-pair Figure 1.6 diagnostic for the stored-input
IEEE-double Horner trace.  The two concrete rounded outputs are proved by the
preceding primitive-operation certificates. -/
theorem ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_one_e13 :
    (1 : ℝ) / 10 ^ 13 <
      |(ieeeDoubleKahanStoredGridRationalFunction 289 -
          kahanRationalFunction (kahanHornerGridPoint 289)) -
        (ieeeDoubleKahanStoredGridRationalFunction 175 -
          kahanRationalFunction (kahanHornerGridPoint 175))| := by
  exact
    ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_one_e13_of_output_values
      ieeeDoubleKahanStoredGridRationalFunction_175_eq
      ieeeDoubleKahanStoredGridRationalFunction_289_eq

/-- Stored-input IEEE-double rounded error at a source-grid point, measured
against the exact rational-function reference at the original source grid
point. -/
noncomputable def ieeeDoubleKahanStoredGridError (k : ℕ) : ℝ :=
  ieeeDoubleKahanStoredGridRationalFunction k -
    kahanRationalFunction (kahanHornerGridPoint k)

/-- Source-grid existential form of the selected-pair Figure 1.6 diagnostic:
two valid grid indices have stored-input IEEE-double rounded errors differing
by more than `10^-13`. -/
theorem exists_ieeeDoubleKahanStoredGridRationalFunction_grid_error_spread_gt_one_e13 :
    ∃ k l : ℕ,
      1 ≤ k ∧ k ≤ 361 ∧ 1 ≤ l ∧ l ≤ 361 ∧
        (1 : ℝ) / 10 ^ 13 <
          |(ieeeDoubleKahanStoredGridRationalFunction l -
              kahanRationalFunction (kahanHornerGridPoint l)) -
            (ieeeDoubleKahanStoredGridRationalFunction k -
              kahanRationalFunction (kahanHornerGridPoint k))| := by
  refine ⟨175, 289, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_one_e13

/-- The selected-pair diagnostic in terms of the named stored-grid error
sequence. -/
theorem exists_ieeeDoubleKahanStoredGridError_pair_spread_gt_one_e13 :
    ∃ k l : ℕ,
      1 ≤ k ∧ k ≤ 361 ∧ 1 ≤ l ∧ l ≤ 361 ∧
        (1 : ℝ) / 10 ^ 13 <
          |ieeeDoubleKahanStoredGridError l -
            ieeeDoubleKahanStoredGridError k| := by
  simpa [ieeeDoubleKahanStoredGridError] using
    exists_ieeeDoubleKahanStoredGridRationalFunction_grid_error_spread_gt_one_e13

/-- Nonconstancy corollary for Figure 1.6: the modeled stored-input
IEEE-double rounded-error sequence on the source grid is not constant.  This
uses the certified selected pair, not an enumeration of all 361 points. -/
theorem not_forall_ieeeDoubleKahanStoredGridError_eq_on_source_grid :
    ¬ ∀ k l : ℕ, 1 ≤ k → k ≤ 361 → 1 ≤ l → l ≤ 361 →
      ieeeDoubleKahanStoredGridError k = ieeeDoubleKahanStoredGridError l := by
  intro hconst
  rcases exists_ieeeDoubleKahanStoredGridError_pair_spread_gt_one_e13 with
    ⟨k, l, hk1, hk361, hl1, hl361, hspread⟩
  have heq : ieeeDoubleKahanStoredGridError l =
      ieeeDoubleKahanStoredGridError k := by
    simpa [eq_comm] using hconst k l hk1 hk361 hl1 hl361
  have hzero :
      |ieeeDoubleKahanStoredGridError l -
        ieeeDoubleKahanStoredGridError k| = 0 := by
    rw [heq, sub_self, abs_zero]
  have hpos : (0 : ℝ) < (1 : ℝ) / 10 ^ 13 := by norm_num
  nlinarith

end NumStability
