# Chapter 3 Problem 3.11 Bottleneck Ledger

Source: `References/Chapter03_full.pdf`, printed page 86, Problem 3.11.

Status: **RED BOTTLENECK: platform-specific rounded traces open.**

Problem 3.11 asks for an error analysis explaining the MATLAB routine

```matlab
y = x.^2;
for i = 1:m
  y = sqrt(y);
end
z = y;
for i = 1:m-1
  z = z.^2;
end
```

and its reported outputs on a 486DX workstation and a Sun SPARCstation, both
using IEEE standard double precision arithmetic.

## Target Paper-Level Theorem Family

The final closed theorem family must prove, for the displayed source vector
`[0.25, 0.5, 0.75, 1.25, 1.5, 2.0]`, that the formalized rounded MATLAB trace
produces:

- 486DX, `m = 50`: `[0.2528, 0.5028, 0.7788, 1.2840, 1.4550, 2.1170]` after
  the source's displayed decimal output rounding;
- 486DX, `m = 75`: `[1, 1, 1, 1, 1, 1]`;
- Sun SPARCstation, `m = 75`: `[0, 0, 0, 1, 1, 1]`;
- and an explanation of why the machine outputs differ.

Candidate final Lean theorem names:

- `kahanAbsoluteProblem311_i486M50_displayed_outputs`
- `kahanAbsoluteProblem311_i486M75_displayed_outputs`
- `kahanAbsoluteProblem311_sunM75_displayed_outputs`
- `kahanAbsoluteProblem311_i486_sun_outputs_differ`

## Dependency Checklist

| Dependency | Status | Evidence / next action |
|---|---:|---|
| Exact real baseline: the routine computes `|x|` without rounding. | CLOSED | `kahanAbsoluteExactFromSquareSteps_eq_abs`, `kahanAbsoluteExact_fifty_eq_abs`, `kahanAbsoluteExact_seventyFive_eq_abs`. |
| Displayed source input vector and output rows represented locally. | CLOSED | `kahanAbsoluteProblem311Inputs`, `kahanAbsoluteProblem311SunM75Outputs`, `kahanAbsoluteProblem311I486M75Outputs`, `kahanAbsoluteProblem311I486M50Outputs`. |
| Concrete finite round-to-even routine surface. | CLOSED | `kahanAbsoluteFiniteSqrtSteps`, `kahanAbsoluteFiniteSquareSteps`, `kahanAbsoluteFiniteRoundToEvenTrace`, and `kahanAbsoluteProblem311FiniteTraceVector` model the rounded initial square, `m` square roots, and `m-1` squarings for a supplied `FloatingPointFormat`. |
| IEEE-double exactness of the initial `x.^2` line on the six source inputs. | CLOSED | `kahanAbsoluteProblem311IeeeDouble_initialSquare_exact` proves the first squaring operation is exact for all displayed inputs under `FloatingPointFormat.ieeeDoubleFormat`; the remaining hardware gap is the long rounded root/square phase. |
| IEEE-double first square-root reduction. | CLOSED | `kahanAbsoluteProblem311Inputs_ieeeDouble_finiteSystem` proves all six source inputs are finite IEEE-double values; `kahanAbsoluteProblem311IeeeDouble_initialSquare_firstSqrt_exact` combines that with the Chapter 2 square-root theorem to prove the first rounded square root after the exact initial square returns the source input; `kahanAbsoluteProblem311FiniteTraceVector_ieeeDouble_m75_eq_reduced` reduces the Sun target to the remaining 74 square roots and 74 squares. |
| IEEE-double fixed points for terminal root/square phases. | CLOSED | `kahanAbsoluteIeeeDoublePredOne` names `1 - 2^-53`; `kahanAbsoluteIeeeDouble_sqrt_predOne` reuses the Chapter 2 double-rounding proof that this predecessor is fixed by rounded square root; `kahanAbsoluteFiniteSqrtSteps_ieeeDouble_predOne`, `kahanAbsoluteIeeeDouble_sqrt_one`, `kahanAbsoluteFiniteSqrtSteps_ieeeDouble_one`, `kahanAbsoluteIeeeDouble_square_one`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_one`, `kahanAbsoluteIeeeDouble_square_zero`, and `kahanAbsoluteFiniteSquareSteps_ieeeDouble_zero` close the fixed-point portions of the remaining Sun trace. |
| IEEE-double first twenty-seven predecessor-square cascade steps. | CLOSED | `kahanAbsoluteIeeeDoubleTwoUlpsBelowOne` names `1 - 2^-52`; `kahanAbsoluteIeeeDoubleFourUlpsBelowOne` names `1 - 2^-51`; `kahanAbsoluteIeeeDoubleEightUlpsBelowOne` names `1 - 2^-50`; `kahanAbsoluteIeeeDoubleSixteenUlpsBelowOne` names `1 - 2^-49`; `kahanAbsoluteIeeeDoubleThirtyTwoUlpsBelowOne` names `1 - 2^-48`; `kahanAbsoluteIeeeDoubleSixtyFourUlpsBelowOne` names `1 - 2^-47`; `kahanAbsoluteIeeeDoubleOneHundredTwentyEightUlpsBelowOne` names `1 - 2^-46`; `kahanAbsoluteIeeeDoubleTwoHundredFiftySixUlpsBelowOne` names `1 - 2^-45`; `kahanAbsoluteIeeeDoubleFiveHundredTwelveUlpsBelowOne` names `1 - 2^-44`; `kahanAbsoluteIeeeDoubleOneThousandTwentyFourUlpsBelowOne` names `1 - 2^-43`; `kahanAbsoluteIeeeDoubleTwoThousandFortyEightUlpsBelowOne` names `1 - 2^-42`; `kahanAbsoluteIeeeDoubleFourThousandNinetySixUlpsBelowOne` names `1 - 2^-41`; `kahanAbsoluteIeeeDoubleEightThousandOneHundredNinetyTwoUlpsBelowOne` names `1 - 2^-40`; `kahanAbsoluteIeeeDoubleSixteenThousandThreeHundredEightyFourUlpsBelowOne` names `1 - 2^-39`; `kahanAbsoluteIeeeDoubleThirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne` names `1 - 2^-38`; `kahanAbsoluteIeeeDoubleSixtyFiveThousandFiveHundredThirtySixUlpsBelowOne` names `1 - 2^-37`; `kahanAbsoluteIeeeDoubleOneHundredThirtyOneThousandSeventyTwoUlpsBelowOne` names `1 - 2^-36`; `kahanAbsoluteIeeeDoubleTwoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne` names `1 - 2^-35`; `kahanAbsoluteIeeeDoubleFiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne` names `1 - 2^-34`; `kahanAbsoluteIeeeDoubleOneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne` names `1 - 2^-33`; `kahanAbsoluteIeeeDoubleTwoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne` names `1 - 2^-32`; `kahanAbsoluteIeeeDoubleFourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne` names `1 - 2^-31`; `kahanAbsoluteIeeeDoubleEightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne` names `1 - 2^-30`; `kahanAbsoluteIeeeDoubleSixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne` names `1 - 2^-29`; `kahanAbsoluteIeeeDoubleThirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne` names `1 - 2^-28`; `kahanAbsoluteIeeeDoubleSixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne` names `1 - 2^-27`; `kahanAbsoluteIeeeDoubleOneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne` names `1 - 2^-26`; `kahanAbsoluteIeeeDouble_square_predOne_eq_twoUlpsBelowOne` proves `fl((1 - 2^-53)^2) = 1 - 2^-52`; `kahanAbsoluteIeeeDouble_square_twoUlpsBelowOne_eq_fourUlpsBelowOne` proves `fl((1 - 2^-52)^2) = 1 - 2^-51`; `kahanAbsoluteIeeeDouble_square_fourUlpsBelowOne_eq_eightUlpsBelowOne` proves `fl((1 - 2^-51)^2) = 1 - 2^-50`; `kahanAbsoluteIeeeDouble_square_eightUlpsBelowOne_eq_sixteenUlpsBelowOne` proves `fl((1 - 2^-50)^2) = 1 - 2^-49`; `kahanAbsoluteIeeeDouble_square_sixteenUlpsBelowOne_eq_thirtyTwoUlpsBelowOne` proves `fl((1 - 2^-49)^2) = 1 - 2^-48`; `kahanAbsoluteIeeeDouble_square_thirtyTwoUlpsBelowOne_eq_sixtyFourUlpsBelowOne` proves `fl((1 - 2^-48)^2) = 1 - 2^-47`; `kahanAbsoluteIeeeDouble_square_sixtyFourUlpsBelowOne_eq_oneHundredTwentyEightUlpsBelowOne` proves `fl((1 - 2^-47)^2) = 1 - 2^-46`; `kahanAbsoluteIeeeDouble_square_oneHundredTwentyEightUlpsBelowOne_eq_twoHundredFiftySixUlpsBelowOne` proves `fl((1 - 2^-46)^2) = 1 - 2^-45`; `kahanAbsoluteIeeeDouble_square_twoHundredFiftySixUlpsBelowOne_eq_fiveHundredTwelveUlpsBelowOne` proves `fl((1 - 2^-45)^2) = 1 - 2^-44`; `kahanAbsoluteIeeeDouble_square_fiveHundredTwelveUlpsBelowOne_eq_oneThousandTwentyFourUlpsBelowOne` proves `fl((1 - 2^-44)^2) = 1 - 2^-43`; `kahanAbsoluteIeeeDouble_square_oneThousandTwentyFourUlpsBelowOne_eq_twoThousandFortyEightUlpsBelowOne` proves `fl((1 - 2^-43)^2) = 1 - 2^-42`; `kahanAbsoluteIeeeDouble_square_twoThousandFortyEightUlpsBelowOne_eq_fourThousandNinetySixUlpsBelowOne` proves `fl((1 - 2^-42)^2) = 1 - 2^-41`; `kahanAbsoluteIeeeDouble_square_fourThousandNinetySixUlpsBelowOne_eq_eightThousandOneHundredNinetyTwoUlpsBelowOne` proves `fl((1 - 2^-41)^2) = 1 - 2^-40`; `kahanAbsoluteIeeeDouble_square_eightThousandOneHundredNinetyTwoUlpsBelowOne_eq_sixteenThousandThreeHundredEightyFourUlpsBelowOne` proves `fl((1 - 2^-40)^2) = 1 - 2^-39`; `kahanAbsoluteIeeeDouble_square_sixteenThousandThreeHundredEightyFourUlpsBelowOne_eq_thirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne` proves `fl((1 - 2^-39)^2) = 1 - 2^-38`; `kahanAbsoluteIeeeDouble_square_thirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne_eq_sixtyFiveThousandFiveHundredThirtySixUlpsBelowOne` proves `fl((1 - 2^-38)^2) = 1 - 2^-37`; `kahanAbsoluteIeeeDouble_square_sixtyFiveThousandFiveHundredThirtySixUlpsBelowOne_eq_oneHundredThirtyOneThousandSeventyTwoUlpsBelowOne` proves `fl((1 - 2^-37)^2) = 1 - 2^-36`; `kahanAbsoluteIeeeDouble_square_oneHundredThirtyOneThousandSeventyTwoUlpsBelowOne_eq_twoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne` proves `fl((1 - 2^-36)^2) = 1 - 2^-35`; `kahanAbsoluteIeeeDouble_square_twoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne_eq_fiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne` proves `fl((1 - 2^-35)^2) = 1 - 2^-34`; `kahanAbsoluteIeeeDouble_square_fiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne_eq_oneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne` proves `fl((1 - 2^-34)^2) = 1 - 2^-33`; `kahanAbsoluteIeeeDouble_square_oneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne_eq_twoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne` proves `fl((1 - 2^-33)^2) = 1 - 2^-32`; `kahanAbsoluteIeeeDouble_square_twoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne_eq_fourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne` proves `fl((1 - 2^-32)^2) = 1 - 2^-31`; `kahanAbsoluteIeeeDouble_square_fourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne_eq_eightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne` proves `fl((1 - 2^-31)^2) = 1 - 2^-30`; `kahanAbsoluteIeeeDouble_square_eightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne_eq_sixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne` proves `fl((1 - 2^-30)^2) = 1 - 2^-29`; `kahanAbsoluteIeeeDouble_square_sixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne_eq_thirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne` proves `fl((1 - 2^-29)^2) = 1 - 2^-28`; `kahanAbsoluteIeeeDouble_square_thirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne_eq_sixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne` proves `fl((1 - 2^-28)^2) = 1 - 2^-27`; `kahanAbsoluteIeeeDouble_square_sixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne_eq_oneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne` proves `fl((1 - 2^-27)^2) = 1 - 2^-26` by the IEEE tie-to-even midpoint rule; and the corresponding `kahanAbsoluteFiniteSquareSteps_ieeeDouble_*_succ` lemmas through `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentySeven_succ` rewrite the remaining square cascade from those first lower values. |
| IEEE-double twenty-eighth predecessor-square cascade step. | CLOSED | `kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne` names the exact non-endpoint state `1 - 134217727 * 2^-52`; `kahanAbsoluteIeeeDouble_square_oneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne_eq_twoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne` proves `fl((1 - 2^-26)^2) = 1 - 134217727 * 2^-52`; `kahanAbsoluteFiniteSquareSteps_ieeeDouble_oneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne_succ` and `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyEight_succ` peel the cascade through that state. |
| IEEE-double twenty-ninth predecessor-square cascade step. | CLOSED | `kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne` names the next state `1 - 536870900 * 2^-53` (`0x1.fffffe000000cp-1`); `kahanAbsoluteIeeeDouble_square_twoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne_eq_fiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne` proves `fl((1 - 134217727 * 2^-52)^2) = 1 - 536870900 * 2^-53`; `kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne_succ` and `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyNine_succ` peel the cascade through that state. |
| IEEE-double thirtieth predecessor-square cascade step. | CLOSED | `kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne` names the next state `1 - 1073741768 * 2^-53` (`0x1.fffffc0000038p-1`); `kahanAbsoluteIeeeDouble_square_fiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne_eq_oneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne` proves `fl((1 - 536870900 * 2^-53)^2) = 1 - 1073741768 * 2^-53`; `kahanAbsoluteFiniteSquareSteps_ieeeDouble_fiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne_succ` and `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_thirty_succ` peel the cascade through that state. |
| IEEE-double one-step square underflow terminal condition. | CLOSED | `kahanAbsoluteIeeeDouble_square_eq_zero_of_abs_mul_lt_half_minSubnormal` proves a rounded IEEE-double square is zero whenever the exact square is strictly below half the smallest subnormal magnitude; `kahanAbsoluteFiniteSquareSteps_ieeeDouble_eq_zero_of_abs_mul_lt_half_minSubnormal` lifts this to all remaining square steps using the zero fixed point. |
| Conditional Sun-style threshold-collapse theorem. | CLOSED | `kahanAbsoluteProblem311_sunM75_outputs_of_phase_laws` proves the displayed Sun `m = 75` row from HP-style threshold phase laws applied to the initial `x^2`. |
| Conditional 486DX all-one-collapse theorem. | CLOSED | `kahanAbsoluteProblem311_i486M75_outputs_of_allOne_phase_laws` proves the displayed 486DX `m = 75` row from all-one phase laws. |
| Concrete Sun SPARCstation phase laws from IEEE-double square/sqrt/square trace. | OPEN | Exact Lean target remains `kahanAbsoluteProblem311SunM75IeeeDoubleTraceTarget`, now equivalent by `kahanAbsoluteProblem311SunM75IeeeDoubleTraceTarget_iff_reduced` to the smaller `kahanAbsoluteProblem311SunM75IeeeDoubleReducedTraceTarget`: prove `kahanAbsoluteProblem311IeeeDoubleReducedM75TraceVector = kahanAbsoluteProblem311SunM75Outputs`. The fixed points after reaching `1 - 2^-53`, `1`, or `0` are closed, the first thirty predecessor-square transitions through `1 - 1073741768 * 2^-53` are closed, and the final underflow-to-zero step is closed once a square input satisfies the half-min-subnormal threshold. Still open: prove the three below-one root phases reach `1 - 2^-53`, prove the three above-one root phases reach `1`, and prove the remaining square cascade from `1 - 1073741768 * 2^-53` reaches a state whose exact square is strictly below half the smallest subnormal before the 74th square. |
| Concrete 486DX `m = 75` all-one phase laws. | OPEN | Need formal x87/486DX semantics: extended precision registers versus stored double values, square-root rounding, register-spill behavior, and how MATLAB's loop stores intermediates. |
| Concrete 486DX `m = 50` numerical rounded trace. | OPEN | Need a formal primitive-operation trace producing values that display as `0.2528`, `0.5028`, `0.7788`, `1.2840`, `1.4550`, and `2.1170`. This is not implied by the threshold-collapse theorems. |
| Decimal display intervals for MATLAB output rows. | CLOSED | `decimal4DisplaysAs`, `vectorDecimal4DisplaysAs`, `kahanAbsoluteProblem311_sunM75_display4_self`, `kahanAbsoluteProblem311_i486M75_display4_self`, `kahanAbsoluteProblem311_i486M50_display4_self`, `kahanAbsoluteProblem311_sunM75_display4_of_phase_laws`, and `kahanAbsoluteProblem311_i486M75_display4_of_allOne_phase_laws`. This is a sufficient four-decimal interval certificate, not a full MATLAB `format short` text-layout or tie-policy formalization. |

## Current Lean Surface

File: `LeanFpAnalysis/FP/Algorithms/KahanAbsolute.lean`

- `kahanAbsoluteExactFromSquareSteps`
- `kahanAbsoluteExactFromSquareSteps_eq_abs`
- `kahanAbsoluteExact_fifty_eq_abs`
- `kahanAbsoluteExact_seventyFive_eq_abs`
- `kahanAbsoluteProblem311Inputs`
- `kahanAbsoluteProblem311SunM75Outputs`
- `kahanAbsoluteProblem311I486M75Outputs`
- `kahanAbsoluteProblem311I486M50Outputs`
- `decimal4HalfUlp`
- `decimal4DisplaysAs`
- `vectorDecimal4DisplaysAs`
- `decimal4HalfUlp_pos`
- `decimal4DisplaysAs_self`
- `vectorDecimal4DisplaysAs_self`
- `kahanAbsoluteProblem311_sunM75_display4_self`
- `kahanAbsoluteProblem311_i486M75_display4_self`
- `kahanAbsoluteProblem311_i486M50_display4_self`
- `kahanAbsolutePhaseTrace`
- `kahanAbsoluteProblem311TraceVector`
- `kahanAbsoluteFiniteSqrtSteps`
- `kahanAbsoluteFiniteSqrtSteps_succ_eq_steps_after_one`
- `kahanAbsoluteFiniteSquareSteps`
- `kahanAbsoluteFiniteRoundToEvenTrace`
- `kahanAbsoluteProblem311FiniteTraceVector`
- `kahanAbsoluteIeeeDoublePredOne`
- `kahanAbsoluteIeeeDoubleTwoUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleFourUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleEightUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleSixteenUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleThirtyTwoUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleSixtyFourUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleOneHundredTwentyEightUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleTwoHundredFiftySixUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleFiveHundredTwelveUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleOneThousandTwentyFourUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleTwoThousandFortyEightUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleFourThousandNinetySixUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleEightThousandOneHundredNinetyTwoUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleSixteenThousandThreeHundredEightyFourUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleThirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleSixtyFiveThousandFiveHundredThirtySixUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleOneHundredThirtyOneThousandSeventyTwoUlpsBelowOne`, `kahanAbsoluteIeeeDoubleTwoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne`, `kahanAbsoluteIeeeDoubleFiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleOneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleTwoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleFourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleEightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne`
- `kahanAbsoluteIeeeDoubleSixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne`
- `kahanAbsoluteProblem311IeeeDouble_initialSquare_exact`
- `kahanAbsoluteIeeeDouble_sqrt_predOne`
- `kahanAbsoluteFiniteSqrtSteps_ieeeDouble_predOne`
- `kahanAbsoluteIeeeDouble_sqrt_one`
- `kahanAbsoluteFiniteSqrtSteps_ieeeDouble_one`
- `kahanAbsoluteIeeeDouble_square_one`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_one`
- `kahanAbsoluteIeeeDouble_square_zero`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_zero`
- `kahanAbsoluteIeeeDouble_square_predOne_eq_twoUlpsBelowOne`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_succ`
- `kahanAbsoluteIeeeDouble_square_twoUlpsBelowOne_eq_fourUlpsBelowOne`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoUlpsBelowOne_succ`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_two_succ`
- `kahanAbsoluteIeeeDouble_square_fourUlpsBelowOne_eq_eightUlpsBelowOne`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_fourUlpsBelowOne_succ`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_three_succ`
- `kahanAbsoluteIeeeDouble_square_eightUlpsBelowOne_eq_sixteenUlpsBelowOne`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_eightUlpsBelowOne_succ`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_four_succ`
- `kahanAbsoluteIeeeDouble_square_sixteenUlpsBelowOne_eq_thirtyTwoUlpsBelowOne`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_sixteenUlpsBelowOne_succ`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_five_succ`
- `kahanAbsoluteIeeeDouble_square_thirtyTwoUlpsBelowOne_eq_sixtyFourUlpsBelowOne`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_thirtyTwoUlpsBelowOne_succ`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_six_succ`
- `kahanAbsoluteIeeeDouble_square_sixtyFourUlpsBelowOne_eq_oneHundredTwentyEightUlpsBelowOne`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_sixtyFourUlpsBelowOne_succ`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_seven_succ`
- `kahanAbsoluteIeeeDouble_square_oneHundredTwentyEightUlpsBelowOne_eq_twoHundredFiftySixUlpsBelowOne`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_oneHundredTwentyEightUlpsBelowOne_succ`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_eight_succ`
- `kahanAbsoluteIeeeDouble_square_twoHundredFiftySixUlpsBelowOne_eq_fiveHundredTwelveUlpsBelowOne`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoHundredFiftySixUlpsBelowOne_succ`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_nine_succ`
- `kahanAbsoluteIeeeDouble_square_fiveHundredTwelveUlpsBelowOne_eq_oneThousandTwentyFourUlpsBelowOne`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_fiveHundredTwelveUlpsBelowOne_succ`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_ten_succ`
- `kahanAbsoluteIeeeDouble_square_oneThousandTwentyFourUlpsBelowOne_eq_twoThousandFortyEightUlpsBelowOne`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_oneThousandTwentyFourUlpsBelowOne_succ`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_eleven_succ`
- `kahanAbsoluteIeeeDouble_square_twoThousandFortyEightUlpsBelowOne_eq_fourThousandNinetySixUlpsBelowOne`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoThousandFortyEightUlpsBelowOne_succ`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twelve_succ`
- `kahanAbsoluteIeeeDouble_square_fourThousandNinetySixUlpsBelowOne_eq_eightThousandOneHundredNinetyTwoUlpsBelowOne`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_fourThousandNinetySixUlpsBelowOne_succ`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_thirteen_succ`
- `kahanAbsoluteIeeeDouble_square_eightThousandOneHundredNinetyTwoUlpsBelowOne_eq_sixteenThousandThreeHundredEightyFourUlpsBelowOne`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_eightThousandOneHundredNinetyTwoUlpsBelowOne_succ`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_fourteen_succ`
- `kahanAbsoluteIeeeDouble_square_sixteenThousandThreeHundredEightyFourUlpsBelowOne_eq_thirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_sixteenThousandThreeHundredEightyFourUlpsBelowOne_succ`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_fifteen_succ`
- `kahanAbsoluteIeeeDouble_square_thirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne_eq_sixtyFiveThousandFiveHundredThirtySixUlpsBelowOne`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_thirtyTwoThousandSevenHundredSixtyEightUlpsBelowOne_succ`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_sixteen_succ`
- `kahanAbsoluteIeeeDouble_square_sixtyFiveThousandFiveHundredThirtySixUlpsBelowOne_eq_oneHundredThirtyOneThousandSeventyTwoUlpsBelowOne`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_sixtyFiveThousandFiveHundredThirtySixUlpsBelowOne_succ`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_seventeen_succ`, `kahanAbsoluteIeeeDouble_square_oneHundredThirtyOneThousandSeventyTwoUlpsBelowOne_eq_twoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_oneHundredThirtyOneThousandSeventyTwoUlpsBelowOne_succ`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_eighteen_succ`, `kahanAbsoluteIeeeDouble_square_twoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne_eq_fiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoHundredSixtyTwoThousandOneHundredFortyFourUlpsBelowOne_succ`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_nineteen_succ`
- `kahanAbsoluteIeeeDouble_square_fiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne_eq_oneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_fiveHundredTwentyFourThousandTwoHundredEightyEightUlpsBelowOne_succ`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twenty_succ`
- `kahanAbsoluteIeeeDouble_square_oneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne_eq_twoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_oneMillionFortyEightThousandFiveHundredSeventySixUlpsBelowOne_succ`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyOne_succ`
- `kahanAbsoluteIeeeDouble_square_twoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne_eq_fourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoMillionNinetySevenThousandOneHundredFiftyTwoUlpsBelowOne_succ`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyTwo_succ`
- `kahanAbsoluteIeeeDouble_square_fourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne_eq_eightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_fourMillionOneHundredNinetyFourThousandThreeHundredFourUlpsBelowOne_succ`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyThree_succ`
- `kahanAbsoluteIeeeDouble_square_eightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne_eq_sixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_eightMillionThreeHundredEightyEightThousandSixHundredEightUlpsBelowOne_succ`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyFour_succ`
- `kahanAbsoluteIeeeDouble_square_sixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne_eq_thirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_sixteenMillionSevenHundredSeventySevenThousandTwoHundredSixteenUlpsBelowOne_succ`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyFive_succ`
- `kahanAbsoluteIeeeDouble_square_thirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne_eq_sixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_thirtyThreeMillionFiveHundredFiftyFourThousandFourHundredThirtyTwoUlpsBelowOne_succ`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentySix_succ`
- `kahanAbsoluteIeeeDouble_square_sixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne_eq_oneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_sixtySevenMillionOneHundredEightThousandEightHundredSixtyFourUlpsBelowOne_succ`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentySeven_succ`
- `kahanAbsoluteIeeeDoubleTwoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne`, `kahanAbsoluteIeeeDouble_square_oneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne_eq_twoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_oneHundredThirtyFourMillionTwoHundredSeventeenThousandSevenHundredTwentyEightUlpsBelowOne_succ`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyEight_succ`
- `kahanAbsoluteIeeeDoubleFiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne`, `kahanAbsoluteIeeeDouble_square_twoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne_eq_fiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoHundredSixtyEightMillionFourHundredThirtyFiveThousandFourHundredFiftyFourUlpsBelowOne_succ`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_twentyNine_succ`
- `kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne`, `kahanAbsoluteIeeeDouble_square_fiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne_eq_oneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_fiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne_succ`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_thirty_succ`
- `kahanAbsoluteIeeeDouble_square_eq_zero_of_abs_mul_lt_half_minSubnormal`
- `kahanAbsoluteFiniteSquareSteps_ieeeDouble_eq_zero_of_abs_mul_lt_half_minSubnormal`
- `kahanAbsoluteProblem311Inputs_ieeeDouble_finiteSystem`
- `kahanAbsoluteProblem311IeeeDouble_initialSquare_firstSqrt_exact`
- `kahanAbsoluteProblem311IeeeDoubleReducedM75TraceVector`
- `kahanAbsoluteProblem311FiniteTraceVector_ieeeDouble_m75_eq_reduced`
- `kahanAbsoluteProblem311SunM75IeeeDoubleTraceTarget`
- `kahanAbsoluteProblem311SunM75IeeeDoubleReducedTraceTarget`
- `kahanAbsoluteProblem311SunM75IeeeDoubleTraceTarget_iff_reduced`
- `kahanAbsoluteProblem311_sunM75_display4_of_ieeeDouble_trace_target`
- `kahanAbsoluteProblem311_sunM75_display4_of_ieeeDouble_reduced_trace_target`
- `kahanAbsoluteProblem311_sunM75_outputs_of_phase_laws`
- `kahanAbsoluteProblem311_sunM75_display4_of_phase_laws`
- `KahanAbsoluteAllOnePhaseLaws`
- `kahanAbsolutePhaseTrace_eq_one_of_allOne_laws`
- `kahanAbsoluteProblem311_i486M75_outputs_of_allOne_phase_laws`
- `kahanAbsoluteProblem311_i486M75_display4_of_allOne_phase_laws`

## Failed / Ruled-Out Routes

- **Exact arithmetic alone:** ruled out.  Exact arithmetic returns `|x|`, while
  all reported rounded traces differ from `|x|`.
- **Generic `FPModel` relative-error bounds alone:** too weak and too
  nondeterministic. They bound errors but do not determine the platform-specific
  trace or the displayed rows.
- **Phase-law conditional theorem as final closure:** not enough. It is useful
  infrastructure, but the source asks for the actual 486DX/Sun results and why
  they differ. The platform laws must still be instantiated from concrete
  semantics.
- **Naive global doubled-ulp square law:** ruled out as a faithful route. The
  first thirty predecessor-square transitions are now proved by IEEE-double
  round-to-even arguments.  The 28th square is `0x1.ffffff0000002p-1`
  (`1 - 134217727 * 2^-52`), the 29th square is
  `0x1.fffffe000000cp-1` (`1 - 536870900 * 2^-53`), and the 30th square is
  `0x1.fffffc0000038p-1` (`1 - 1073741768 * 2^-53`), not the pure endpoints
  predicted by exact ulp doubling. The remaining threshold theorem still needs
  a source-faithful formal trace or a proved batched theorem from this
  non-endpoint state.

## Next Target

The next proof target should be one concrete platform-law instantiation, not
another generic adapter.  The display-interval layer, initial IEEE-double
square, first rounded square root, terminal fixed points, first thirty
predecessor-square transitions, and one-step square underflow-to-zero theorem
are now closed for the represented rows, so the
smallest local route is to attack the reduced Sun `m = 75` target using the
existing finite IEEE-double square-root, squaring, finite-normal, and underflow
infrastructure. The exact Lean proposition to prove is
`kahanAbsoluteProblem311SunM75IeeeDoubleReducedTraceTarget`; by
`kahanAbsoluteProblem311SunM75IeeeDoubleTraceTarget_iff_reduced` this closes
`kahanAbsoluteProblem311SunM75IeeeDoubleTraceTarget`. The next smaller
dependencies are the below-one root-hit facts, the above-one root-hit facts, and
the remaining square cascade's threshold-reach fact starting from
`1 - 1073741768 * 2^-53`. If the finite IEEE-double
semantics are not the source-faithful Sun semantics because the historical
MATLAB/SPARCstation path used different store/load or underflow behavior, the
next action is to define that platform-specific phase routine explicitly and
replace this target by the corrected routine.

The `m = 50` 486DX trace is probably the harder route because it requires
actual numerical finite-operation iteration rather than a threshold law.
