# Higham Chapter 5 Derivative-Evaluation Bottleneck

## Scope

- Source: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
  Chapter 5, equations (5.5)-(5.7), Algorithm 5.2.
- Split: 1.
- Status: closed. The source-strength first-order derivative estimate is now
  proved by a direct coupled Algorithm 5.2 backward-error argument. The earlier
  computed-quotient/source-budget route remains as an auxiliary finite
  decomposition, but it is no longer the selected-scope blocker.

## Closed source claim

The selected source claim is the first-derivative forward-error bound
`|p'(alpha) - rhat_0| <= 2*n*u*ptilde'(alpha) + O(u^2)`, derived from the
bidiagonal perturbation forms (5.5)-(5.6).

## Current Lean closure

- `polyDescDerivAbs` formalizes the derivative absolute majorant `ptilde'`.
- `polyDescPairsDeriv`, `polyDescPairsDerivPerturbed`, and
  `polyDescPairsDerivAbs` provide the derivative analogue of the
  coefficientwise perturbation infrastructure used for (5.3).
- `abs_polyDescPairsDerivPerturbed_sub_polyDescPairsDeriv_le` proves that
  coefficient perturbations bounded by `eta` perturb the derivative by at most
  `eta * polyDescPairsDerivAbs`.
- `fl_hornerDerivativeFold_snd_backward_error_coefficients` proves the coupled
  fold-level backward-error expansion for the rounded first-derivative
  component.
- `fl_hornerDerivativeDesc_snd_backward_error_coefficients_coupled` packages the
  rounded derivative output as the exact derivative of a
  coefficientwise-perturbed polynomial with perturbations bounded by
  `gamma fp (2*(coeffsDesc.length-1))`.
- `fl_hornerDerivativeDesc_snd_forward_error_bound_coupled` proves the direct
  finite forward bound
  `gamma fp (2*(coeffsDesc.length-1)) * polyDescDerivAbs x coeffsDesc`.
- `fl_hornerDerivativeDescFirstOrderRemainder` names the explicit
  quadratic-and-higher gamma remainder.
- `fl_hornerDerivativeDesc_first_derivative_error_bound` proves the displayed
  first-order form
  `2*n*u*ptilde' + fl_hornerDerivativeDescFirstOrderRemainder`.
- `polyDescAbs_hornerSyntheticQuotientDesc_le_polyDescDerivAbs` proves the exact
  synthetic-quotient majorant bridge.
- `fl_hornerSyntheticQuotientDesc_eval_forward_error_bound` bounds the computed
  quotient evaluation error by the recursive finite `quotientBudget`.
- `fl_hornerDerivativeDesc_snd_forward_error_bound_with_derivAbs_and_eval_majorant`
  proves the finite derivative bound
  `gamma*(ptilde' + quotientBudget) + quotientBudget`.
- `fl_hornerStepForwardErrorBudget_le_abs_inputs` bounds each local budget step
  by rounded input data.
- `fl_hornerStepForwardErrorBudget_le_exact_abs_plus_error` replaces the rounded
  value input in one local budget by the exact value accumulator plus an
  explicit propagated error.
- `fl_hornerSyntheticQuotientEvalForwardSourceMajorant` and
  `fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant` define the
  exact-accumulator source budget.
- `fl_hornerSyntheticQuotientDescEvalForwardMajorant_le_source_majorant` proves
  that the finite rounded-data quotient budget is dominated by this source
  budget.
- `fl_hornerDerivativeDesc_snd_forward_error_bound_with_derivAbs_and_source_majorant`
  gives the derivative bound with the source-shaped quotient budget.
- `fl_hornerDerivativeDescFirstOrderSourceRemainder` names the exact remaining
  term after extracting the displayed `2*n*u*ptilde'` coefficient.
- `fl_hornerDerivativeDesc_snd_forward_error_bound_first_order_source_remainder`
  proves the first-order display form with that named remainder.

The direct coupled theorem closes the printed (5.7) without needing to show
that the auxiliary source-budget remainder is quadratic. That older route is
kept because it still explains the (5.5)-(5.6) quotient/bidiagonal split, but
the selected first-order derivative gate is now discharged by
`fl_hornerDerivativeDesc_first_derivative_error_bound`.

## Closed Lean theorem family

Closed family:

- `polyDescPairsDeriv_eq_polyDescDeriv_map_fst`
- `polyDescPairsDerivAbs_eq_polyDescDerivAbs_map_fst`
- `abs_polyDescPairsDerivPerturbed_sub_polyDescPairsDeriv_le`
- `fl_hornerDerivativeFold_snd_backward_error_coefficients`
- `fl_hornerDerivativeDesc_snd_backward_error_coefficients_coupled`
- `fl_hornerDerivativeDesc_snd_forward_error_bound_coupled`
- `fl_hornerDerivativeDescFirstOrderRemainder_eq_zero_of_u_eq_zero`
- `fl_hornerDerivativeDesc_first_derivative_error_bound`

Proof shape:

1. Prove a derivative perturbation adapter for pair lists.
2. Prove a coupled backward-error induction for the rounded derivative
   component, keeping the value and derivative recurrences in the same
   `gamma(2n)` envelope.
3. Apply the derivative perturbation adapter to obtain the finite
   `gamma(2n)*ptilde'` forward bound.
4. Split `gamma(2n)` into its linear term plus the exact rational
   quadratic-and-higher remainder.

## Superseded auxiliary routes

- Finite recursive quotient majorant route: useful and proved, but leaves
  `quotientBudget` opaque if used as the sole path to the first-order theorem.
- Exact quotient-majorant route: closed for the exact quotient, but does not by
  itself bound the rounded quotient or its recursive budget.
- Local rounded-data budget route: closed through
  `fl_hornerSyntheticQuotientDescEvalForwardMajorant_le_source_majorant`, which
  expresses the rounded intermediate accumulators in exact-accumulator source
  terms. This remains useful documentation for (5.5)-(5.6), but the direct
  coupled proof bypasses its source-remainder simplification.

## Optional follow-up

A cosmetic scalar-variable `isBigO` wrapper can be added for
`fl_hornerDerivativeDescFirstOrderRemainder`. It is not needed for the selected
finite theorem because the remainder is already the explicit
`((2n*u)^2)/(1-2n*u) * ptilde'` term.

## Validation command

Focused validation:

```bash
lake env lean LeanFpAnalysis/FP/Algorithms/Horner.lean
lake build LeanFpAnalysis.FP.Algorithms.Horner
lake env lean examples/LibraryLookup.lean
lake env lean /private/tmp/higham_ch5_horner_axioms.lean
```
