# Chapter 4 Compensated-Summation Bottleneck Ledger

## Scope

- Source: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
  Chapter 4, Section 4.3, equation (4.8).
- Selected claim: Algorithm 4.2 returns
  `s_hat_n = sum_i x_i * (1 + mu_i)` with
  `|mu_i| <= 2*u + O(n*u^2)`.
- Blocking downstream rows: equation (4.9), because the existing forward-error
  theorem is conditional on the missing backward-error representation.
- Status: active bottleneck. The empirical Figure 4.2 and Problem 4.10 research
  rows are non-gating and are not part of this bottleneck.

## Exact Blocking Theorem Family

The current smallest source-shaped Lean target is the returned-stored-sum
coefficient collapse:

```lean
theorem kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_two_u_plus_majorant
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (k : Nat) (hk : k <= n)
    (huSmall : fp.u <= 1 / 64)
    (i : Fin (kahanCoupledCoeffSteps fp v k hk).length)
    (hBudget :
      (C0 + C1 *
        (((kahanCoupledCoeffSteps fp v k hk).drop (i.val + 1)).length : Real)) *
          fp.u <= 1) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    |(kahanCoupledSourceCoeff steps i).s - 1| <=
      2 * fp.u +
        (C0 + C1 * ((steps.drop (i.val + 1)).length : Real)) * fp.u ^ 2
```

The constants `C0` and `C1` may be loose, but the first-order term must remain
`2*u`, not `14*u`, `O(n*u)`, or a data-dependent residual divided by
`sum_i |x_i|`.

Once this coefficient theorem exists, the chapter-level closure theorem should
instantiate the now-available conditional bridge
`fl_kahanSum_backward_error_source_bound_of_sourceCoeff_s_bound`, then feed the
already-proved `fl_kahanSum_forward_error_bound_of_backward`.

## Dependency Checklist

| Dependency | Local status | Evidence |
|---|---|---|
| Algorithm 4.2 rounded trace and prefix state | available-local | `KahanStepTrace`, `kahanStepTrace`, `kahanPrefixState`, `fl_kahanState`, `fl_kahanSum` |
| Finite-format exact first step from zero state | available-local | `finiteKahanStepTrace_zero_of_finiteSystem`, `finiteKahanStep_zero_of_finiteSystem`, `finiteKahanPrefixState_one_of_finiteSystem`; proves the concrete finite round-to-even wrapper maps finite input `x` and initial `s=0,e=0` to `s=x,e=0`, including at the one-element prefix-state level. This is a coherence fact absent from bare `FPModel`. |
| Bare-`FPModel` exact first step from zero state | rejected-route | `kahanStepTrace_abstractCounterexample_zero`, `kahanStep_abstractCounterexample_zero_ne_exact`, and `not_forall_kahanStep_zero_exact` show that the current abstract model alone does not force the first step to ingest a nonzero input exactly from `s=0,e=0`; finite-format/coherence hypotheses are genuinely needed. |
| Bare-`FPModel` returned `2*u+O(u^2)` shortcut | rejected-route | `kahanBiasedSmallCounterexampleFPModel`, `kahanBiasedTwoStepInput`, `fl_kahanSum_biasedSmallCounterexample_twoStep`, `fl_kahanSum_biasedSmallCounterexample_twoStep_of_pos_lt_one`, `not_exists_fl_kahanSum_biasedSmallCounterexample_twoStep_source_bound_of_Cu_le_half`, and `not_forall_fl_kahanSum_backward_error_source_bound_bare_fpmodel_exactSubConstants` show that, for any second-order constant `C` with `C*u <= 1/2`, the abstract relative-error contract can make the returned value on `[1,0]` exceed the `2*u+C*u^2` coefficient cap. In particular, `u=1/1000` rejects promoting the conditional exact-subtraction constants to a bare-model theorem. |
| Abstract exact-zero-path bridge | available-local | `kahanStepTrace_zero_of_exact_zero_path`, `kahanStep_zero_of_exact_zero_path`, and `kahanPrefixState_one_of_exact_zero_path` isolate the right-zero add, exact `0-x` subtraction, and exact `(-x)+x` cancellation hypotheses sufficient for the source first-step initialization. |
| Direct returned-sum coefficient expansion | available-local | `kahanCoupledSourceCoeff`, `kahanCoupledSourceUnroll_s_eq_sum_sourceCoeff`, `kahanCoupledCoeffSteps_prefixState_s_eq_sum_sourceCoeff` |
| Paired `(s+e,e)` source coefficient expansion | available-local | `kahanCoupledSourceTotalCoeff`, `kahanCoupledCoeffSteps_prefixState_total_eq_sum_sourceTotalCoeff` |
| Paired-total source-shaped coefficient bound | available-local | `kahanCoupledCoeffSteps_sourceTotalCoeff_abs_sub_one_le_two_u_plus_majorant` |
| Paired-total source-shaped backward-error witness | available-local | `fl_kahanCompensatedTotal_backward_error_source_bound` |
| Product-radius collapse for the affine total route | available-local | `kahanAffineInputCoeffProductRadius_le_two_u_plus` |
| Returned-sum residual absorption and source-scaled residual bridge | conditional foundation/rejected input-majorant route | `kahanAffineCoeffSteps_prefixSum_exists_mu_abs_le_productRadius`, `kahanAffineCoeffSteps_prefixSum_exists_mu_abs_le_of_productRadius_and_residualBudget`, and `fl_kahanSum_backward_error_source_bound_of_affine_residualBudget` remove the division-by-`sum |x|` artifact if the propagated retained-correction residual is bounded by `C*n*u^2*sum_i |x_i|`. The route audit theorems `not_kahanAffine_residualBudget_inputMajorant_one_of_Cu_le_one` and `not_exists_kahanAffine_residualBudget_inputMajorant_fixed_C` prove that the current input-only retained-correction majorant cannot supply such a fixed second-order estimate, even on one exact input. |
| Goldberg phantom exact zero-input step | available-local | `kahanCoupledExactZeroStep`, `kahanCoupledExactZeroStep_next`, `kahanCoupledExactZeroStep_propagate`, `kahanCoupledCoeffFold_append_exactZeroStep`, `kahanCoupledCoeffPropagate_append_exactZeroStep`, `kahanCoupledSourceUnroll_append_exactZeroStep`, `kahanCoupledSourceCoeff_append_exactZeroStep_s_eq_sourceTotalCoeff`, `kahanCoupledSourceCoeff_append_exactZeroStep_e_eq_zero` |
| Returned-coordinate recurrence from paired `(s+e,e)` coefficients | available-local | `KahanState.returnedFromTotalCorrection`, `KahanCoupledCoeffStep.returnedStateCoeff`, `KahanCoupledCoeffStep.returnedCorrectionCoeff`, `KahanCoupledCoeffStep.propagateTotalCorrection_returned`, `kahanCoupledCoeffSteps_propagateTotalCorrection_returnedDev_abs_le` |
| Returned source coefficient as paired returned coordinate | available-local | `kahanCoupledSourceCoeff_s_eq_returned_totalCorrectionPropagate` identifies `(kahanCoupledSourceCoeff steps i).s` with `KahanState.returnedFromTotalCorrection` of the paired-coordinate propagated source coefficient. |
| Triangle-route returned coefficient bound | rejected-route/available-local | `kahanCoupledSourceCoeff_s_abs_sub_one_le_pairedCoeffMajorant_sum` and `kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_pairedCoeffMajorant_sum` bound the returned source coefficient by paired-total majorant plus paired correction majorant. This is formal evidence for the rejected triangle route; the extra correction majorant is first order. |
| General residual-cancellation algebra layer | available-local | `kahanCorrectionInputCoeff_sub_stateCoeff_add_deltaSub_eq`, `kahanCorrectionInputCoeff_sub_stateCoeff_add_deltaSub_abs_le_seven_u_sq`, `kahanCoupledCoeffStepOfWitness_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq`, `kahanCoupledCoeffStepOfIndex_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq`, `kahanCoupledCoeffSteps_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq`, and `kahanCoupledCoeffStepsOfWitnesses_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq` expose the local and prefix-indexed non-exact-subtraction cancellation: the paired correction residual is `-deltaSub` plus a second-order remainder. `kahanTotalResidualCoeff_sub_correctionResidualCoeff_sub_deltaY_eq`, `kahanTotalResidualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq`, `kahanCoupledCoeffStepOfWitness_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq`, `kahanCoupledCoeffStepOfIndex_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq`, `kahanCoupledCoeffSteps_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq`, and `kahanCoupledCoeffStepsOfWitnesses_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq` expose the companion relation `totalResidual - correctionResidual = deltaY + O(u^2)`. The combined theorem family `kahanTotalResidualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq`, `kahanCoupledCoeffStepOfWitness_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq`, `kahanCoupledCoeffStepOfIndex_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq`, `kahanCoupledCoeffSteps_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq`, and `kahanCoupledCoeffStepsOfWitnesses_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq` now packages these into the single relation `totalResidual + deltaSub - deltaY = O(u^2)` at raw, witness, actual-index, prefix actual, and prefix explicit-witness levels. Together these form the coefficient-level dependency package for a Goldberg-style returned-sum recurrence that does not assume `deltaSub = 0`; the local-facts and dropped-suffix propagation package is now available, so the remaining task is the source-strength leading-constant/coherence handoff. |
| Suffix-local recurrence facts alone | rejected-route/available-local | `highamCh4KahanSuffixCounterexampleLocalFacts`, `highamCh4KahanSuffixCounterexampleStep1_localFacts`, `highamCh4KahanSuffixCounterexampleStep2_localFacts`, `highamCh4KahanSuffixCounterexampleReturnedCoeff_eq`, `highamCh4KahanSuffixMajorant_step`, `highamCh4KahanSuffixMajorant_recurrence`, `highamCh4KahanSuffixMajorant_update_of_localFacts`, `highamCh4KahanSuffixMajorant_propagate_of_localFacts_aux`, `highamCh4KahanSuffixMajorant_propagate_of_localFacts`, `kahanCoupledCoeffStepOfIndex_localFacts`, `kahanCoupledCoeffSteps_localFacts`, `kahanCoupledCoeffSteps_totalCorrectionPropagate_abs_le_correctedSuffixMajorant`, `kahanCoupledCoeffSteps_drop_localFacts`, `kahanCoupledCoeffSteps_drop_totalCorrectionPropagate_abs_le_correctedSuffixMajorant`, `kahanCoupledCoeffSteps_sourceTotalCorrectionCoeff_abs_le_correctedSuffixMajorant`, `highamCh4KahanReturnedFinalStep_majorant`, `highamCh4KahanReturnedAppendFinal_majorant`, `highamCh4KahanReturnedNonempty_majorant`, `kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_correctedReturnedMajorant`, `fl_kahanSum_backward_error_source_bound_correctedReturnedMajorant`, `highamCh4KahanSuffixCounterexampleReturnedCoeff_abs_sub_one_eq`, `highamCh4KahanSuffixCounterexampleReturnedCoeff_abs_sub_one_le_three_u_plus_four_u_sq`, and `highamCh4KahanSuffixCounterexample_not_two_u_plus_K_u_sq` show that two symbolic suffix steps can satisfy the available local cancellation facts while their returned coefficient equals `(1+u)^3`, with exact error `3*u + 3*u^2 + u^3`, violating every fixed `2*u + K*u^2` returned-cap for sufficiently small positive `u`. The corrected-route recurrence propagates through a list of local-fact steps, proving `|final.s-1| <= 2*u + (9+13*m)*u^2` and `|final.e| <= 3*u` for `kahanCoupledTotalCorrectionPropagate`; the final-step/list-splitting package then proves the ordinary returned coefficient and full `fl_kahanSum` backward-error representation with leading `3*u`. A genuinely stronger finite-format/coherence recurrence or primary-source correction is still needed before claiming the printed ordinary returned leading `2*u` statement. |
| Exact-subtraction coefficient layer | available-local/conditional | `kahanTotalStateCoeff_abs_sub_one_le_u_sq_of_deltaSub_zero`, `kahanTotalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_deltaSub_zero`, `kahanTotalResidualCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero`, `kahanCorrectionStateCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero`, `kahanCorrectionInputCoeff_abs_le_u_plus_three_u_sq_of_deltaSub_zero`, and `kahanCorrectionResidualCoeff_abs_le_two_u_sq_of_deltaSub_zero` show that if the correction-subtraction delta is zero, the paired correction residual becomes second order. |
| Exact-subtraction returned coefficient collapse | conditional foundation | `kahanCoupledCoeffStepsExactSub`, `kahanCoupledPairedCoeffMajorant_exactSubConstants_le_one_u_plus`, `kahanCoupledSourceCoeff_s_abs_sub_one_le_exactSubMajorant`, and `kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_two_u_plus_exactSubMajorant` prove the ordinary returned source-coefficient bound `2*u + O(m*u^2)` under the explicit prefix hypothesis that every chosen correction-subtraction delta is zero. |
| Four-term finite returned-trace obstruction | concrete obstruction/available-local | `highamCh4KahanReturnedCounterexampleP5Format` and `highamCh4KahanReturnedCounterexampleP5_rounding` prove the explicit p=5 finite round-to-even identities suggested by the GPT-5.5 Pro follow-up. With those identities, `highamCh4KahanReturnedCounterexampleP5_state_eq`, `highamCh4KahanReturnedCounterexample_exactSum`, `highamCh4KahanReturnedCounterexample_absSum`, `highamCh4KahanReturnedCounterexample_muLowerBound`, `highamCh4KahanReturnedCounterexample_no_source_bound_of_lt`, `highamCh4KahanReturnedCounterexample_no_source_bound_two_div_p`, and `highamCh4KahanReturnedCounterexampleP5_no_source_bound_one_sixteenth_actual` prove that the p=5 returned trace has error `22`, cannot be represented with all source weights bounded by `1/16 = 2u`, and that any same-identity trace with scale `p > 26` cannot satisfy the pure first-order budget `2/p`. This is a concrete obstruction to a pure first-order `2u` returned-coordinate cap, not by itself a refutation of a sufficiently loose explicit `2u+O(nu^2)` statement. |
| Explicit exact-sub witness-family route | conditional foundation | `exists_kahanStepTrace_deltaWitness_of_exact_sub`, `KahanPrefixCorrectionSubExact`, `kahanPrefixDeltaWitnessFamilyOfExactSub`, `kahanCoupledCoeffStepsOfWitnessesExactSub`, `kahanCoupledCoeffStepsOfWitnesses_sourceCoeff_s_abs_sub_one_le_two_u_plus_exactSubMajorant`, `kahanCoupledCoeffStepsOfWitnesses_prefixState_s_eq_sum_sourceCoeff`, `fl_kahanSum_backward_error_source_bound_of_exactSubWitnesses`, and `fl_kahanSum_backward_error_source_bound_of_exactSubTrace` prove the full returned-sum backward-error representation from exact correction subtraction in the actual prefix trace. The finite bridge `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sub_finite` derives that theorem from finite correction-subtraction representability; `FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_sub_finite` and `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sub_finite` show it is enough to prove direct finite representability only on nonzero prefix indices, with index `0` closed by `temp = 0`; `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sterbenzLe` and `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fergusonLe` derive it from all-index inclusive Sterbenz/Ferguson conditions; `FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_sterbenzLe`, `FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_fergusonLe`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sterbenzLe`, and `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_fergusonLe` handle index `0` by `temp = 0` and require Sterbenz/Ferguson only on tail steps; `KahanPrefixCorrectionSubExact.of_finiteRoundToEven_fastTwoSumCertificates` derives it from per-step FastTwoSum certificates; `KahanPrefixFastTwoSumFiniteCertificates.of_base2_abs_gt` derives those certificates from all-step base-2 finite/order/range hypotheses; `KahanPrefixFastTwoSumFiniteCertificates.of_first_exact_and_tail_base2_abs_gt` handles the initialized first step by finite zero-add exactness and requires order/range only on tail steps; `finiteKahanTrace_temp_finiteSystem`, `finiteKahanTrace_y_finiteSystem`, and `finiteKahanTrace_s_finiteSystem` discharge the named finite-coordinate fields, while `FloatingPointFormat.not_forall_finiteSystem_sub_finiteSystem` blocks the finite-coordinate-only shortcut, `not_forall_finiteKahanTrace_tail_sterbenzLe` blocks unconditional tail inclusive Sterbenz, `not_forall_finiteKahanTrace_tail_fergusonLe` blocks unconditional tail inclusive Ferguson, and `not_forall_finiteKahanTrace_tail_direct_sub_finite` blocks unconditional direct tail finite correction-subtraction. |
| Conditional bridge from returned coefficient bound to `fl_kahanSum` backward-error witness | available-local | `fl_kahanSum_backward_error_source_bound_of_sourceCoeff_s_bound`, `fl_kahanSum_backward_error_source_bound_of_witnessSourceCoeff_s_bound`, `fl_kahanSum_backward_error_source_bound_of_exactSubWitnesses`, `fl_kahanSum_backward_error_source_bound_of_exactSubTrace`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sub_finite`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sub_finite`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fastTwoSumCertificates`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_abs_gt`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_abs_gt_of_order_range`, and `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_tail_order_range` |
| Transfer from paired-total coefficient to returned `s` coefficient with only second-order loss | conditionalized | Triangle splitting through `(kahanCoupledSourceCoeff steps i).e` gives a first-order loss under the general paired majorant. The exact-subtraction route now proves the source-shaped returned coefficient bound, but only under `kahanCoupledCoeffStepsExactSub`; bare `FPModel` still exposes a first-order old-state coefficient and does not justify that exact-sub hypothesis. |
| Source-shaped final backward-error theorem for `fl_kahanSum` | blocked on deriving a sufficient arbitrary-trace finite/coherence condition | The returned-sum theorem is proved under `fl_kahanSum_backward_error_source_bound_of_exactSubTrace`, under `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sub_finite`, under direct tail finite representability via `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sub_finite`, under all-index `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sterbenzLe` and `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fergusonLe`, under tail-only `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sterbenzLe` and `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_fergusonLe`, under `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fastTwoSumCertificates`, under `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_abs_gt`, under `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_abs_gt_of_order_range`, and under `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_tail_order_range`. The theorem `not_forall_finiteKahanTrace_tail_abs_order` shows the tail-order FastTwoSum hypothesis is not derivable for arbitrary input order, `not_forall_finiteKahanTrace_tail_sterbenzLe` shows tail inclusive Sterbenz is not derivable for arbitrary input order, `not_forall_finiteKahanTrace_tail_fergusonLe` shows tail inclusive Ferguson is not derivable for arbitrary input order, `not_forall_finiteKahanTrace_tail_direct_sub_finite` shows direct tail finite correction-subtraction is not derivable for arbitrary input order, and `FloatingPointFormat.not_forall_finiteSystem_sub_finiteSystem` shows finite coordinates alone do not give direct finite subtraction. The theorem `not_exists_kahanAffine_residualBudget_inputMajorant_fixed_C` also rejects the current input-majorant affine residual estimate as a fixed second-order route. A refined affine residual/cancellation theorem or a non-FastTwoSum coefficient recurrence under stronger finite-format/coherence hypotheses now define the next targets. |

## Failed Or Rejected Local Routes

| Route | Result | Why it does not close (4.8) |
|---|---|---|
| Affine residual absorption for the returned sum using the current input-only majorant | Produces exact witnesses via `kahanAffineCoeffSteps_prefixSum_exists_mu_abs_le_productRadius`; the strengthened bridge `kahanAffineCoeffSteps_prefixSum_exists_mu_abs_le_of_productRadius_and_residualBudget` and final wrapper `fl_kahanSum_backward_error_source_bound_of_affine_residualBudget` prove the desired source shape if the propagated retained-correction residual is bounded by `C*n*u^2*sum_i |x_i|`. | Formally rejected for the current input-only majorant by `not_kahanAffine_residualBudget_inputMajorant_one_of_Cu_le_one` and `not_exists_kahanAffine_residualBudget_inputMajorant_fixed_C`: for one exact input, the final retained-correction majorant is first order in `u`, so no fixed nonnegative `C` can bound it by `C*u^2*sum_i |x_i|` uniformly in small `u`. |
| Triangle split from paired total to returned sum | Formalized by `kahanCoupledSourceCoeff_s_abs_sub_one_le_pairedCoeffMajorant_sum` and the concrete `kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_pairedCoeffMajorant_sum`. | The available retained-correction coefficient bound is first-order, so the proved bound contains the paired correction majorant in addition to the paired-total term; this is too weak for the source's `2*u + O(n*u^2)` result. |
| Exact-subtraction paired route | Formalized conditionally by `kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_two_u_plus_exactSubMajorant`, the explicit witness-family theorem `fl_kahanSum_backward_error_source_bound_of_exactSubWitnesses`, the operation-level theorem `fl_kahanSum_backward_error_source_bound_of_exactSubTrace`, the finite-subtraction theorem `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sub_finite`, the tail-direct finite-subtraction theorem `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sub_finite`, the all-index inclusive Sterbenz/Ferguson theorems `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sterbenzLe` and `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fergusonLe`, the tail-only Sterbenz/Ferguson theorems `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sterbenzLe` and `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_fergusonLe`, the finite-certificate theorem `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fastTwoSumCertificates`, the base-2 theorem `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_abs_gt`, the reduced theorem `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_abs_gt_of_order_range`, and the first-exact/tail-order theorem `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_tail_order_range`. | This route has the correct `2*u + O(n*u^2)` shape and avoids arbitrary witness selection under finite correction-subtraction hypotheses, but the simple arbitrary-input routes are formally ruled out: finite coordinates alone, tail order, tail inclusive Sterbenz, tail inclusive Ferguson, and direct tail finite correction-subtraction all fail in Lean. |
| Arbitrary finite returned `2u` cap | Formalized as a concrete obstruction by `highamCh4KahanReturnedCounterexampleP5_no_source_bound_one_sixteenth_actual`. | In the explicit p=5 round-to-even trace, the returned sum differs from the exact sum by `22` while `sum |x_i| = 346`, forcing coefficient radius at least `11/173 > 1/16 = 2u`. This rejects the pure first-order returned cap, but it does not refute a sufficiently loose explicit `2u+O(n*u^2)` theorem. |
| Suffix recurrence from only the current local facts | Formalized as a symbolic obstruction by `highamCh4KahanSuffixCounterexample_not_two_u_plus_K_u_sq`, with corrected-shape audit `highamCh4KahanSuffixCounterexampleReturnedCoeff_abs_sub_one_le_three_u_plus_four_u_sq`, leading-3 list recurrence `highamCh4KahanSuffixMajorant_propagate_of_localFacts`, actual-step local-facts bridge `kahanCoupledCoeffStepOfIndex_localFacts`, dropped-suffix wrapper `kahanCoupledCoeffSteps_drop_totalCorrectionPropagate_abs_le_correctedSuffixMajorant`, and actual source-total specialization `kahanCoupledCoeffSteps_sourceTotalCorrectionCoeff_abs_le_correctedSuffixMajorant`. | The two-step symbolic audit satisfies the local facts currently available from the residual-cancellation layer, but its returned coefficient `(1+u)^3` has error `3*u + 3*u^2 + u^3` and exceeds `1 + 2*u + K*u^2` for every fixed nonnegative `K` and sufficiently small positive `u`. The corrected leading-3 theorem now applies to actual Kahan source-total coefficients; a proof of Higham's ordinary returned leading-2 statement needs an extra coherence invariant or a different coefficient recurrence. |
| Direct stored-sum product recurrence | Uses `kahanStoredSumStateCoeff = 1 + deltaS` and `kahanStoredSumInputCoeff = (1+deltaY)(1+deltaS)`. | This route loses the cancellation with the retained correction and gives an `O(n*u)` product accumulation, not the compensated `O(u) + O(n*u^2)` behavior. |
| Direct paired returned-coordinate recurrence under bare `FPModel` | Uses `KahanCoupledCoeffStep.propagateTotalCorrection_returned`. | The formal recurrence identifies the returned old-state coefficient as the direct stored-sum coefficient `A`, with `|A-1| <= u`. This confirms the current abstract model route needs additional finite-format/coherence structure before it can recover Higham's second-order suffix accumulation. |
| Bare-`FPModel` first-step exactness | Tries to derive `kahanStep fp x KahanState.zero = {s := x, e := 0}` from the abstract standard model alone. | Ruled out by `not_forall_kahanStep_zero_exact`: the existing abstract model satisfies the `FPModel` axioms but may have `fl_add x 0` round a nonzero input to zero. Use the concrete finite-format wrapper or add explicit right-zero/coherence hypotheses. |
| Bare-`FPModel` returned cap from exact-sub constants | Tries to close the ordinary returned source theorem for all `FPModel`s with a `2*u+C*u^2` cap, including the exact-subtraction-route constant. | Ruled out by `not_exists_fl_kahanSum_biasedSmallCounterexample_twoStep_source_bound_of_Cu_le_half` and `not_forall_fl_kahanSum_backward_error_source_bound_bare_fpmodel_exactSubConstants`: a small-unit-roundoff abstract model satisfying the local relative-error contract returns `1003004003001/1000000000000` on `[1,0]`, so the unique first coefficient exceeds the stated cap. |

## Proof-Source Ledger

| Selected claim | Missing proof step | External source and exact location | Assumptions/constants | Intended Lean target | Route/status | Local closure theorem |
|---|---|---|---|---|---|---|
| Higham Ch. 4 Eq. (4.8) | Check whether a pure first-order `2u` returned-Kahan source cap survives concrete finite round-to-even arithmetic. | GPT-5.5 Pro via Oracle browser session `higham-ch4-kahan-returned-strict`, using compact math-only prompt `chapter_splitting/oracle_prompts/higham_ch4_kahan_returned_strict_followup.tex`. No book PDF, repository bulk export, secrets, or long source excerpt was sent. | Advisory result proposed a p=5, four-term trace with inputs `(-22,-68,-248,8)` and returned state `(-352,8)`, giving exact sum `-330`, returned error `22`, and coefficient lower bound `11/173 > 1/16 = 2u`. | Prove the p=5 finite round-to-even identities and instantiate the obstruction for the concrete format; use it as source-mismatch evidence for the printed ordinary-return leading-`2u` claim. | advisory fully formalized for the concrete p=5 pure-`2u` obstruction and generalized to conditional `p > 26` pure `2/p` cap failure | `highamCh4KahanReturnedCounterexampleP5_rounding`, `highamCh4KahanReturnedCounterexampleP5_state_eq`, `highamCh4KahanReturnedCounterexample_muLowerBound`, `highamCh4KahanReturnedCounterexample_no_source_bound_two_div_p`, `highamCh4KahanReturnedCounterexampleP5_no_source_bound_one_sixteenth_actual` |
| Higham Ch. 4 Eq. (4.8) | Decide whether the current local residual-cancellation facts are sufficient for a `2*u+K*u^2` returned-source coefficient recurrence. | GPT-5.5 Pro via Oracle browser session `higham-ch4-kahan-suffix-recurrence`, using compact math-only prompt `chapter_splitting/oracle_prompts/higham_ch4_kahan_suffix_recurrence_prompt.tex`. No book PDF, repository bulk export, secrets, or long source excerpt was sent. | Advisory result proposed two symbolic suffix steps satisfying the local facts, with returned coefficient `(1+u)^3`; it also suggested that a corrected route likely needs a stronger coherence hypothesis or a larger leading constant. | Formalize the two-step insufficiency counterexample and use it to motivate the corrected leading-`3u` ordinary-return theorem. | advisory formalized as route-elimination theorem, with exact expansion and leading-3 symbolic bound; positive corrected theorem now formalized in the whole-problem row below | `highamCh4KahanSuffixCounterexampleStep1_localFacts`, `highamCh4KahanSuffixCounterexampleStep2_localFacts`, `highamCh4KahanSuffixCounterexampleReturnedCoeff_eq`, `highamCh4KahanSuffixCounterexampleReturnedCoeff_abs_sub_one_eq`, `highamCh4KahanSuffixCounterexampleReturnedCoeff_abs_sub_one_le_three_u_plus_four_u_sq`, `highamCh4KahanSuffixCounterexample_not_two_u_plus_K_u_sq` |
| Higham Ch. 4 Eq. (4.8) | Ask for the next hidden/coherence invariant or corrected recurrence after the suffix-local obstruction. | GPT-5.5 Pro via Oracle browser session `higham-ch4-kahan-hidden-coherence` returned only a non-answer plan sentence. Retry session `higham-ch4-hidden-coherence-retry` used compact math-only prompt `chapter_splitting/oracle_prompts/higham_ch4_kahan_hidden_coherence_retry.tex`. No book PDF, repository bulk export, secrets, or long source excerpt was sent. | Retry advised a corrected leading-`3*u` theorem surface with recurrence variables `alpha=|z-1|` and `beta=|q|`, including update constants `13` for `alpha` and preserved `beta <= 3*u` under `u <= 1/64`. | Translate the local-facts update, arithmetic step, finite-horizon induction, list propagation theorem, actual-step/dropped-suffix local-facts package, and source-total specialization; accept the corrected leading-`3u` returned theorem surface for the ordinary returned value. | retry advisory formalized as corrected-route source-total theorem for actual Kahan coefficients; leading-`2u` ordinary-return theorem is now recorded as source-mismatched rather than open | `highamCh4KahanSuffixMajorant_update_of_localFacts`, `highamCh4KahanSuffixMajorant_step`, `highamCh4KahanSuffixMajorant_recurrence`, `highamCh4KahanSuffixMajorant_propagate_of_localFacts`, `kahanCoupledCoeffStepOfIndex_localFacts`, `kahanCoupledCoeffSteps_drop_totalCorrectionPropagate_abs_le_correctedSuffixMajorant`, `kahanCoupledCoeffSteps_sourceTotalCorrectionCoeff_abs_le_correctedSuffixMajorant` |
| Higham Ch. 4 Eq. (4.8) | Whole-problem source-statement audit: check whether the ordinary returned `2*u+O(n*u^2)` claim is false, too strong, or missing hypotheses. | GPT-5.5 Pro via Oracle browser session `higham-ch4-eq48-whole-audit`, using reviewed whole-problem packet `chapter_splitting/oracle_prompts/higham_ch4_eq48_whole_problem_audit.tex`. No book PDF, repository bulk export, secrets, or long source excerpt was sent. | Advisory conclusion: interpreted as an arbitrary-input ordinary returned-sum theorem under the stated relative-error model, Eq. (4.8) is false/misstated; the missing term is the final main-sum rounding, giving ordinary returned leading `3*u`, while leading `2*u` survives for compensated total or under an extra exact-subtraction/correlation condition. Hallman-Ipsen, *Precision-aware deterministic and probabilistic error bounds for floating point summation*, Eq. (4.7), gives the corrected leading-`3*u` factor for the ordinary returned compensated-summation result. | Treat the printed leading-`2u` row as SOURCE-MISMATCH-CORRECTED. The corrected ordinary returned leading-`3*u` source-coefficient theorem and full `fl_kahanSum` backward-error representation are formalized. Separately keep/label the exact-subtraction leading-`2*u` theorem as conditional. | closed for corrected ordinary-return theorem; printed leading-`2u` row disposition recorded | `kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_correctedReturnedMajorant`, `fl_kahanSum_backward_error_source_bound_correctedReturnedMajorant`; source-row disposition recorded as SOURCE-MISMATCH-CORRECTED for the ordinary returned value |
| Higham Ch. 4 Eq. (4.8) | Coefficient proof for returned Kahan sum, preserving cancellation with retained correction. | David Goldberg, "What Every Computer Scientist Should Know About Floating-Point Arithmetic", ACM Computing Surveys 1991, Oracle reprint Appendix D, Theorem 8 discussion around lines 1567-1615: coefficient proof for Kahan summation via `s_k - c_k` and `c_k`, with a final zero-input step. URL: https://docs.oracle.com/cd/E19957-01/806-3568/ncg_goldberg.html | Standard model deltas bounded by machine epsilon; informal `O(epsilon^2)` and `O(n*epsilon^2)` terms require explicit constants for Lean. The local Lean audit now shows the bare abstract `FPModel` recurrence for returned `s` exposes a first-order old-state coefficient, `not_forall_kahanStep_zero_exact` rules out deriving the source first-step initialization from `FPModel` alone, and `not_exists_fl_kahanSum_biasedSmallCounterexample_twoStep_source_bound_of_Cu_le_half` rules out promoting any fixed `2*u+C*u^2` returned cap to all bare `FPModel`s in the small-`u` regime. The exact-subtraction trace layer proves the source-shaped returned theorem if every displayed correction subtraction is exact; the general residual-cancellation layer now proves that, without exact subtraction, the paired correction residual is `-deltaSub + O(u^2)`, `totalResidual - correctionResidual = deltaY + O(u^2)`, and, in combined form, `totalResidual + deltaSub - deltaY = O(u^2)`, both for individual witnesses and for prefix-indexed actual/explicit witness families. The finite bridge derives the exact-sub route from direct correction-subtraction representability, direct tail finite correction-subtraction with the first index closed by `temp = 0`, all-index or tail-only inclusive Sterbenz conditions, all-index or tail-only inclusive Ferguson conditions, or per-step `FastTwoSumFiniteCertificate`s. The base-2 bridge derives FastTwoSum certificates from finite/order/range hypotheses, finite coordinates are automatic for the finite trace, but `FloatingPointFormat.not_forall_finiteSystem_sub_finiteSystem` proves finite coordinates alone do not imply finite exact subtraction, and the initialized first step is closed by exact finite zero-addition or by `temp = 0` in the tail finite-subtraction routes. Formal counterexamples show the tail-order FastTwoSum, tail inclusive Sterbenz, tail inclusive Ferguson, and direct tail finite-subtraction bridges cannot close arbitrary input order. The current input-majorant affine residual estimate is also formally rejected by `not_exists_kahanAffine_residualBudget_inputMajorant_fixed_C`. | Prove the suffix coefficient recurrence that absorbs the combined residual-cancellation algebra into the returned source coefficients, or find a non-FastTwoSum coefficient cancellation under a stronger finite-format/coherence model. | partial foundation: compensated-total source-shaped witness, returned-coordinate obstruction, returned-source paired-coordinate bridge, formally rejected triangle-route bound, general and combined residual-cancellation algebra, exact-subtraction conditional returned coefficient bound, explicit witness-family returned theorem, exact-sub trace theorem, finite-subtraction/tail finite-subtraction/all-index and tail Sterbenz/Ferguson returned theorems, finite FastTwoSum certificate theorem, all-step base-2 order/range returned theorem, first-exact/tail-order returned theorem, finite-coordinate trace theorem, finite-coordinate-only subtraction counterexample, tail-order counterexample, tail-Sterbenz counterexample, tail-Ferguson counterexample, direct tail finite-subtraction counterexample, affine input-majorant residual counterexample, final conditional bridge, finite-format exact first-step coherence, bare-model exact-start counterexample, biased small-`u` returned-cap counterexamples, and exact-zero-path bridge formalized; arbitrary-trace finite/coherence proof open | `kahanCorrectionInputCoeff_sub_stateCoeff_add_deltaSub_eq`, `kahanCorrectionInputCoeff_sub_stateCoeff_add_deltaSub_abs_le_seven_u_sq`, `kahanCoupledCoeffStepOfWitness_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq`, `kahanCoupledCoeffStepOfIndex_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq`, `kahanCoupledCoeffSteps_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq`, `kahanCoupledCoeffStepsOfWitnesses_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq`, `kahanTotalResidualCoeff_sub_correctionResidualCoeff_sub_deltaY_eq`, `kahanTotalResidualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq`, `kahanCoupledCoeffStepOfWitness_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq`, `kahanCoupledCoeffStepOfIndex_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq`, `kahanCoupledCoeffSteps_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq`, `kahanCoupledCoeffStepsOfWitnesses_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq`, `kahanTotalResidualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq`, `kahanCoupledCoeffStepOfWitness_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq`, `kahanCoupledCoeffStepOfIndex_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq`, `kahanCoupledCoeffSteps_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq`, `kahanCoupledCoeffStepsOfWitnesses_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq`, `not_kahanAffine_residualBudget_inputMajorant_one_of_Cu_le_one`, `not_exists_kahanAffine_residualBudget_inputMajorant_fixed_C`, `not_forall_finiteKahanTrace_tail_direct_sub_finite`, `not_forall_finiteKahanTrace_tail_fergusonLe`, `not_forall_finiteKahanTrace_tail_sterbenzLe`, `FloatingPointFormat.not_forall_finiteSystem_sub_finiteSystem`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sub_finite`, `FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_sub_finite`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_fergusonLe`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sterbenzLe`, `FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_fergusonLe`, `FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_sterbenzLe`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fergusonLe`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sterbenzLe`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sub_finite`, `FiniteKahanPrefixCorrectionSubFinite.of_fergusonConditionLe`, `FiniteKahanPrefixCorrectionSubFinite.of_sterbenzRatioConditionLe`, `finiteKahanTrace_s_finiteSystem`, `not_exists_fl_kahanSum_biasedSmallCounterexample_twoStep_source_bound_of_Cu_le_half`, `not_forall_fl_kahanSum_backward_error_source_bound_bare_fpmodel_exactSubConstants`, `fl_kahanSum_biasedSmallCounterexample_twoStep_of_pos_lt_one`, `fl_kahanSum_biasedSmallCounterexample_twoStep`, `kahanBiasedSmallCounterexampleFPModel`, `not_forall_finiteKahanTrace_tail_abs_order`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_tail_order_range`, `KahanPrefixFastTwoSumFiniteCertificates.of_first_exact_and_tail_base2_abs_gt`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_abs_gt_of_order_range`, `finiteKahanTrace_temp_finiteSystem`, `finiteKahanTrace_y_finiteSystem`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_abs_gt`, `KahanPrefixFastTwoSumFiniteCertificates.of_base2_abs_gt`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fastTwoSumCertificates`, `KahanPrefixFastTwoSumFiniteCertificates`, `KahanPrefixCorrectionSubExact.of_finiteRoundToEven_fastTwoSumCertificates`, `FiniteKahanPrefixCorrectionSubFinite`, `KahanAddSubFiniteRoundToEvenRealization`, `fl_kahanSum_backward_error_source_bound_of_exactSubTrace`, `KahanPrefixCorrectionSubExact`, `kahanPrefixDeltaWitnessFamilyOfExactSub`, `fl_kahanSum_backward_error_source_bound_of_exactSubWitnesses`, `fl_kahanSum_backward_error_source_bound_of_witnessSourceCoeff_s_bound`, `kahanCoupledCoeffStepsOfWitnesses_sourceCoeff_s_abs_sub_one_le_two_u_plus_exactSubMajorant`, `kahanCoupledCoeffStepsOfWitnessesExactSub`, `KahanPrefixDeltaWitnessFamily`, `kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_two_u_plus_exactSubMajorant`, `kahanCoupledSourceCoeff_s_abs_sub_one_le_exactSubMajorant`, `kahanCoupledPairedCoeffMajorant_exactSubConstants_le_one_u_plus`, `kahanCoupledCoeffStepsExactSub`, `kahanCoupledSourceCoeff_s_abs_sub_one_le_pairedCoeffMajorant_sum`, `kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_pairedCoeffMajorant_sum`, `kahanCoupledSourceCoeff_s_eq_returned_totalCorrectionPropagate`, `kahanStepTrace_zero_of_exact_zero_path`, `kahanStep_zero_of_exact_zero_path`, `kahanPrefixState_one_of_exact_zero_path`, `kahanStepTrace_abstractCounterexample_zero`, `kahanStep_abstractCounterexample_zero_ne_exact`, `not_forall_kahanStep_zero_exact`, `finiteKahanStepTrace_zero_of_finiteSystem`, `finiteKahanStep_zero_of_finiteSystem`, `finiteKahanPrefixState_one_of_finiteSystem`, `fl_kahanCompensatedTotal_backward_error_source_bound`, `fl_kahanSum_backward_error_source_bound_of_sourceCoeff_s_bound`, `KahanCoupledCoeffStep.propagateTotalCorrection_returned`, `kahanCoupledCoeffSteps_propagateTotalCorrection_returnedDev_abs_le`, `kahanCoupledExactZeroStep_next`, `kahanCoupledExactZeroStep_propagate`, `kahanCoupledCoeffFold_append_exactZeroStep`, `kahanCoupledCoeffPropagate_append_exactZeroStep`, `kahanCoupledSourceUnroll_append_exactZeroStep`, `kahanCoupledSourceCoeff_append_exactZeroStep_s_eq_sourceTotalCoeff`, `kahanCoupledSourceCoeff_append_exactZeroStep_e_eq_zero` |
| Higham Ch. 4 Eq. (4.8) | Current input-majorant source-scaled residual estimate for the affine route. | Local affine coefficient route in `CompensatedSum.lean`, derived from Higham's equation (4.8) target and Goldberg's cancellation proof. | Formally false as a fixed second-order estimate: with one exact input, the indexed correction budget is zero but the final input-only retained-correction majorant is first order in `u`. | Replace this input-only residual charge by a refined affine residual/cancellation theorem, or use a stronger finite-format/coherence coefficient proof. | rejected route | `not_kahanAffine_residualBudget_inputMajorant_one_of_Cu_le_one`, `not_exists_kahanAffine_residualBudget_inputMajorant_fixed_C` |
| Higham Ch. 4 Eq. (4.8) | Original compensated-summation source behind Goldberg/Higham. | W. Kahan, "Further remarks on reducing truncation errors", Communications of the ACM, 1965. | Bibliographic source identified; full proof text not acquired in this pass. | Optional historical source acquisition only; Hallman-Ipsen Eq. (4.7) and the local Lean proof close the corrected selected statement. | optional source acquisition fallback | non-gating |
| Higham Ch. 4 Eq. (4.8) | Source-facing final theorem statement and equation numbering. | Local `References/1.9780898718027.ch4.pdf`, Section 4.3, equation (4.8), plus Hallman-Ipsen, *Precision-aware deterministic and probabilistic error bounds for floating point summation*, Eq. (4.7), for the corrected leading constant. | Higham's printed ordinary returned leading-`2u` statement is recorded as a source mismatch; the corrected ordinary returned statement has leading `3u` with explicit higher-order constants in Lean. | `fl_kahanSum_backward_error_source_bound_correctedReturnedMajorant`. | selected source row corrected | closed |

Rows 92 and 93 are historical advisory steps. Their corrected leading-`3*u`
route is now superseded locally by
`fl_kahanSum_backward_error_source_bound_correctedReturnedMajorant`; what
is now closed is the source-row disposition: the printed leading-`2*u`
ordinary-return statement is SOURCE-MISMATCH-CORRECTED, and the corrected
leading-`3*u` theorem is formalized and primary-source checked against
Hallman-Ipsen Eq. (4.7).

## Closed Corrected Target

The concrete p=5 binary finite-format identities are now proved by
`highamCh4KahanReturnedCounterexampleP5_rounding`, and the concrete pure-`2u`
obstruction is closed by
`highamCh4KahanReturnedCounterexampleP5_no_source_bound_one_sixteenth_actual`.
The symbolic suffix-local route is also rejected by
`highamCh4KahanSuffixCounterexample_not_two_u_plus_K_u_sq`.

The combined local cancellation theorems now feed the corrected suffix
majorant through the actual-step and dropped-suffix wrappers
`kahanCoupledCoeffSteps_drop_localFacts`,
`kahanCoupledCoeffSteps_drop_totalCorrectionPropagate_abs_le_correctedSuffixMajorant`,
and `kahanCoupledCoeffSteps_sourceTotalCorrectionCoeff_abs_le_correctedSuffixMajorant`.
The next proof target is therefore no longer list-indexing, local-facts
packaging, source-total initialization, or the corrected ordinary returned
leading-`3*u` theorem.  The whole-problem GPT-5.5 Pro audit treats the printed
ordinary returned leading-`2*u` statement as likely misstated under the current
model, and the source-honest ordinary returned leading-`3*u` theorem is now
formalized by `fl_kahanSum_backward_error_source_bound_correctedReturnedMajorant`.
The primary-source check now supports recording the printed leading-`2*u`
ordinary-return statement as a source mismatch.  Any future leading-`2*u`
theorem must keep the exact extra hypothesis on the theorem surface.
The simple arbitrary-input
finite/coherence shortcuts are now formally ruled out: finite coordinates alone
do not imply finite exact subtraction, tail order is false, tail inclusive
Sterbenz is false, tail inclusive Ferguson is false, and direct tail finite
representability of
`(finiteKahanTrace fmt v i).temp - (finiteKahanTrace fmt v i).s` for
`i.val ≠ 0` is false.  The current input-only affine residual-majorant route is
also formally ruled out by
`not_exists_kahanAffine_residualBudget_inputMajorant_fixed_C`.  The
constructors `FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_sub_finite`,
`FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_sterbenzLe`, and
`FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_fergusonLe`
handle the index `0` subtraction by `temp = 0`.

The returned-source coefficient majorant and the returned `fl_kahanSum`
backward-error representation are now formalized from exact correction
subtraction in the actual prefix trace by
`kahanCoupledCoeffStepsOfWitnesses_sourceCoeff_s_abs_sub_one_le_two_u_plus_exactSubMajorant`
and `fl_kahanSum_backward_error_source_bound_of_exactSubTrace`.  The bridge
`KahanPrefixCorrectionSubExact.of_finiteRoundToEven_fastTwoSumCertificates`
now proves that exact-sub trace condition from
`KahanPrefixFastTwoSumFiniteCertificates`, and
`KahanPrefixFastTwoSumFiniteCertificates.of_first_exact_and_tail_base2_abs_gt`
handles the initialized first step by finite zero-add exactness and builds the
remaining certificates from tail-step base-2 absolute-order/range hypotheses,
but `not_forall_finiteKahanTrace_tail_abs_order` proves those hypotheses are
not derivable for arbitrary input order.  Likewise,
`not_forall_finiteKahanTrace_tail_sterbenzLe` rules out deriving tail inclusive
Sterbenz for arbitrary input order,
`not_forall_finiteKahanTrace_tail_fergusonLe` rules out deriving tail inclusive
Ferguson for arbitrary input order, and
`not_forall_finiteKahanTrace_tail_direct_sub_finite` rules out deriving direct
tail finite correction-subtraction for arbitrary input order.  The general
equation (4.8) proof should therefore stop trying to close the printed
ordinary returned leading-`2*u` theorem as an unconditional arbitrary-input
claim.  It should use the proved corrected ordinary returned leading-`3*u`
theorem for source-honest downstream work, or prove a clearly conditional
leading-`2*u` variant with the exact extra hypothesis on the theorem surface.

The bare abstract `FPModel` route remains rejected: it neither forces exact
first-step initialization nor exact correction subtraction, and the biased
small-`u` model shows the exact-subtraction-route returned cap is false for all
bare `FPModel`s.

## Validation Status

- `lake env lean LeanFpAnalysis\FP\Algorithms\CompensatedSum.lean`: PASS after
  adding the four-term finite returned-Kahan obstruction block and proving the
  concrete p=5 finite rounding identities.
- `lake build LeanFpAnalysis.FP.Algorithms.CompensatedSum`: PASS after adding
  the `highamCh4KahanReturnedCounterexample*` declarations, including
  `highamCh4KahanReturnedCounterexampleP5_rounding`,
  `highamCh4KahanReturnedCounterexample_no_source_bound_two_div_p`, and
  `highamCh4KahanReturnedCounterexampleP5_no_source_bound_one_sixteenth_actual`,
  1485 jobs.
- `lake env lean examples\LibraryLookup.lean`: PASS after adding lookup checks
  for the finite returned-trace obstruction declarations, conditional `p > 26`
  pure-cap obstruction, and concrete p=5 corollaries.
- Focused `#print axioms` for
  `highamCh4KahanReturnedCounterexampleState_eq_of_rounding`,
  `highamCh4KahanReturnedCounterexample_muLowerBound`,
  `highamCh4KahanReturnedCounterexample_no_source_bound_two_div_p`,
  `highamCh4KahanReturnedCounterexampleP5_no_source_bound_one_sixteenth`, and
  `highamCh4KahanReturnedCounterexampleP5_no_source_bound_one_sixteenth_actual`:
  PASS with only standard Mathlib axioms `propext`, `Classical.choice`, and
  `Quot.sound`.
- `lake env lean LeanFpAnalysis\FP\Algorithms\CompensatedSum.lean`: PASS after
  adding the suffix-local recurrence insufficiency theorem.
- `lake build LeanFpAnalysis.FP.Algorithms.CompensatedSum`: PASS after adding
  the `highamCh4KahanSuffixCounterexample*` declarations, 1485 jobs.
- `lake env lean examples\LibraryLookup.lean`: PASS after adding lookup checks
  for the suffix-local recurrence insufficiency declarations.
- Focused `#print axioms` for
  `highamCh4KahanSuffixCounterexampleReturnedCoeff_eq`,
  `highamCh4KahanSuffixMajorant_step`,
  `highamCh4KahanSuffixMajorant_recurrence`,
  `highamCh4KahanSuffixMajorant_update_of_localFacts`,
  `highamCh4KahanSuffixMajorant_propagate_of_localFacts_aux`,
  `highamCh4KahanSuffixMajorant_propagate_of_localFacts`,
  `highamCh4KahanSuffixCounterexampleReturnedCoeff_abs_sub_one_eq`,
  `highamCh4KahanSuffixCounterexampleReturnedCoeff_abs_sub_one_le_three_u_plus_four_u_sq`,
  and `highamCh4KahanSuffixCounterexample_not_two_u_plus_K_u_sq`: PASS with
  only standard Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env lean LeanFpAnalysis\FP\Algorithms\CompensatedSum.lean`: PASS after
  adding `kahanCoupledCoeffStepOfIndex_localFacts`,
  `kahanCoupledCoeffSteps_localFacts`,
  `kahanCoupledCoeffSteps_totalCorrectionPropagate_abs_le_correctedSuffixMajorant`,
  `kahanCoupledCoeffSteps_drop_localFacts`, and
  `kahanCoupledCoeffSteps_drop_totalCorrectionPropagate_abs_le_correctedSuffixMajorant`,
  and PASS again after adding
  `kahanCoupledCoeffSteps_sourceTotalCorrectionCoeff_abs_le_correctedSuffixMajorant`.
- `lake build LeanFpAnalysis.FP.Algorithms.CompensatedSum`: PASS after the
  actual-step, dropped-suffix, and source-total local-facts/majorant bridge declarations,
  1485 jobs.
- `lake env lean tmp\higham_ch4_suffix_actual_axioms.lean`: PASS. Focused
  `#print axioms` for the six actual-step/drop-suffix/source-total bridge declarations
  reports only standard Mathlib axioms `propext`, `Classical.choice`, and
  `Quot.sound`.
- `lake env lean examples\LibraryLookup.lean`: PASS after adding lookup checks
  for the actual-step, dropped-suffix, and source-total local-facts/majorant bridge
  declarations.
- Placeholder scan
  `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis\FP\Algorithms\CompensatedSum.lean examples\LibraryLookup.lean`:
  PASS with no matches.
- `git diff --check -- LeanFpAnalysis\FP\Algorithms\CompensatedSum.lean examples\LibraryLookup.lean chapter_splitting\reports\split1_ch04_core_audit.md chapter_splitting\reports\split1_ch04_compensated_bottleneck.md`:
  PASS; Git reports only existing CRLF normalization warnings for touched files.
- `lake build LeanFpAnalysis.FP.Algorithms.CompensatedSum`: PASS after adding
  the general residual-cancellation algebra lemmas and prefix-indexed wrappers.
- `lake env lean /private/tmp/higham_ch4_general_cancellation_axioms.lean`:
  PASS. Focused `#print axioms` for the general residual-cancellation algebra
  declarations reports only standard Mathlib axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- `lake env lean examples/LibraryLookup.lean`: PASS after adding lookup checks
  for the general residual-cancellation algebra declarations and prefix-indexed
  wrappers.
- Placeholder scan
  `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/CompensatedSum.lean examples/LibraryLookup.lean`:
  PASS with no matches.
- `git diff --check`: PASS after the general residual-cancellation algebra
  and prefix-wrapper update.
- `lake build LeanFpAnalysis.FP.Algorithms.CompensatedSum`: PASS after adding
  the combined residual-cancellation theorem family.
- `lake env lean tmp\higham_ch4_combined_residual_axioms.lean`: PASS before
  cleanup. Focused `#print axioms` for the five combined
  residual-cancellation declarations reports only standard Mathlib axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env lean examples/LibraryLookup.lean`: PASS after adding lookup checks
  for the combined residual-cancellation declarations.
- `lake build LeanFpAnalysis.FP.Algorithms.CompensatedSum`: PASS, 1485 jobs.
- `lake build LeanFpAnalysis.FP.Algorithms.CompensatedSum`: PASS after adding
  finite correction-subtraction/Sterbenz/Ferguson branches, first-step split
  constructors, and tail-only Sterbenz/Ferguson returned-sum wrappers.
- `lake build LeanFpAnalysis.FP.Algorithms.CompensatedSum`: PASS after adding
  `FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_sub_finite`
  and
  `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sub_finite`.
- `lake env lean /private/tmp/higham_ch4_tail_sub_finite_axioms.lean`: PASS.
  Focused `#print axioms` for the direct tail finite-subtraction constructor
  and returned-sum wrapper reports only standard Mathlib axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- `lake env lean examples/LibraryLookup.lean`: PASS after adding lookup checks
  for the direct tail finite-subtraction constructor and returned-sum wrapper.
- `lake build`: PASS after the direct tail finite-subtraction route and report
  updates, 3471 jobs, with only the pre-existing QR/Givens/FastMatMul linter
  warnings.
- `lake build LeanFpAnalysis.FP.Analysis.FloatingPointArithmetic`: PASS after
  adding `FloatingPointFormat.decimalSingleDigitFormat_finiteSystem_nine`,
  `FloatingPointFormat.decimalSingleDigitFormat_not_finiteSystem_eighteen`,
  and `FloatingPointFormat.not_forall_finiteSystem_sub_finiteSystem`.
- `lake env lean /private/tmp/higham_ch4_finite_sub_counterexample_axioms.lean`:
  PASS. Focused `#print axioms` for the finite-subtraction route-elimination
  declarations reports only standard Mathlib axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- `lake env lean examples/LibraryLookup.lean`: PASS after adding lookup checks
  for the finite-subtraction route-elimination declarations.
- `lake build`: PASS after the finite-subtraction route-elimination declarations
  and report updates, 3471 jobs, with only the pre-existing
  QR/Givens/FastMatMul linter warnings.
- `lake build LeanFpAnalysis.FP.Algorithms.CompensatedSum`: PASS after adding
  `not_forall_finiteKahanTrace_tail_sterbenzLe`.
- `lake env lean /private/tmp/higham_ch4_tail_sterbenz_counterexample_axioms.lean`:
  PASS. Focused `#print axioms` for
  `not_forall_finiteKahanTrace_tail_sterbenzLe` reports only standard Mathlib
  axioms `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env lean examples/LibraryLookup.lean`: PASS after adding a lookup check
  for `not_forall_finiteKahanTrace_tail_sterbenzLe`.
- `lake build`: PASS after `not_forall_finiteKahanTrace_tail_sterbenzLe` and
  report updates, 3471 jobs, with only the pre-existing QR/Givens/FastMatMul
  linter warnings.
- `lake build LeanFpAnalysis.FP.Algorithms.CompensatedSum`: PASS after adding
  `not_forall_finiteKahanTrace_tail_fergusonLe`.
- `lake env lean /private/tmp/higham_ch4_tail_ferguson_counterexample_axioms.lean`:
  PASS. Focused `#print axioms` for
  `not_forall_finiteKahanTrace_tail_fergusonLe` reports only standard Mathlib
  axioms `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env lean examples/LibraryLookup.lean`: PASS after adding a lookup check
  for `not_forall_finiteKahanTrace_tail_fergusonLe`.
- Placeholder scan
  `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/CompensatedSum.lean examples/LibraryLookup.lean`:
  PASS with no matches.
- `git diff --check`: PASS after the tail-Ferguson route-elimination update.
- `lake build`: PASS after `not_forall_finiteKahanTrace_tail_fergusonLe` and
  report updates, 3471 jobs, with only the pre-existing QR/Givens/FastMatMul
  linter warnings.
- `lake build LeanFpAnalysis.FP.Analysis.FloatingPointArithmetic`: PASS after
  adding the two-exponent one-digit decimal audit format and
  `FloatingPointFormat.decimalSingleDigitTwoExponentFormat_round_add_one_ninety`.
- `lake build LeanFpAnalysis.FP.Algorithms.CompensatedSum`: PASS after adding
  `not_forall_finiteKahanTrace_tail_direct_sub_finite`.
- `lake env lean /private/tmp/higham_ch4_tail_direct_sub_counterexample_axioms.lean`:
  PASS. Focused `#print axioms` for
  `not_forall_finiteKahanTrace_tail_direct_sub_finite` reports only standard
  Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env lean examples/LibraryLookup.lean`: PASS after adding lookup checks
  for the two-exponent decimal audit format and
  `not_forall_finiteKahanTrace_tail_direct_sub_finite`.
- Placeholder scan
  `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Analysis/FloatingPointArithmetic.lean LeanFpAnalysis/FP/Algorithms/CompensatedSum.lean examples/LibraryLookup.lean`:
  PASS with no matches.
- `git diff --check`: PASS after the direct tail finite-subtraction
  route-elimination update.
- `lake build`: PASS after `not_forall_finiteKahanTrace_tail_direct_sub_finite`
  and report updates, 3471 jobs, with only the pre-existing
  QR/Givens/FastMatMul linter warnings.
- `lake build`: PASS, 3471 jobs. QR/Givens/FastMatMul linter warnings are
  pre-existing baseline warnings outside this Chapter 4 path.
- `lake env lean examples/LibraryLookup.lean`: PASS; the command prints the
  full lookup index.
- `lake env lean /private/tmp/higham_ch4_phantom_lookup.lean`: PASS. Focused
  `#print axioms` for the phantom-step declarations and
  `fl_kahanCompensatedTotal_backward_error_source_bound`, plus the
  returned-coordinate obstruction declarations and
  `fl_kahanSum_backward_error_source_bound_of_sourceCoeff_s_bound` checked in
  `/private/tmp/higham_ch4_returned_lookup.lean`, reports only standard Mathlib
  axioms `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env lean /private/tmp/higham_ch4_exactsub_axioms.lean`: PASS. Focused
  `#print axioms` for the exact-sub coefficient layer, chosen-witness route,
  explicit witness-family route,
  `fl_kahanSum_backward_error_source_bound_of_exactSubTrace`,
  `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fastTwoSumCertificates`,
  `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_abs_gt`,
  `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_abs_gt_of_order_range`,
  and `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_tail_order_range`
  reports only standard Mathlib axioms `propext`, `Classical.choice`, and
  `Quot.sound`.
- `lake env lean /private/tmp/higham_ch4_finite_coherence_axioms.lean`: PASS.
  Focused `#print axioms` for finite trace `s`, all-index and
  first-exact/tail Sterbenz/Ferguson finite-subtraction constructors, and the
  corresponding returned-sum wrappers reports only standard Mathlib axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env lean examples/LibraryLookup.lean`: PASS after adding lookup checks
  for the first-exact/tail-order certificate, tail Sterbenz/Ferguson
  finite-subtraction constructors, and returned-sum theorems.
- `lake build LeanFpAnalysis.FP.Algorithms.CompensatedSum`: PASS after adding
  `kahanAffineCoeffSteps_prefixSum_exists_mu_abs_le_of_productRadius_and_residualBudget`
  and `fl_kahanSum_backward_error_source_bound_of_affine_residualBudget`.
- `lake env lean /private/tmp/higham_ch4_affine_residual_axioms.lean`: PASS.
  Focused `#print axioms` for the affine residual-budget bridge and final
  returned-sum wrapper reports only standard Mathlib axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- `lake env lean examples/LibraryLookup.lean`: PASS after adding lookup checks
  for the affine residual-budget bridge and final returned-sum wrapper.
- `lake build LeanFpAnalysis.FP.Algorithms.CompensatedSum`: PASS after adding
  `not_kahanAffine_residualBudget_inputMajorant_one_of_Cu_le_one` and
  `not_exists_kahanAffine_residualBudget_inputMajorant_fixed_C`.
- `lake env lean /private/tmp/higham_ch4_affine_inputmajorant_counterexample_axioms.lean`:
  PASS. Focused `#print axioms` for the affine input-majorant residual
  counterexamples reports only standard Mathlib axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- `lake env lean examples/LibraryLookup.lean`: PASS after adding lookup checks
  for the affine input-majorant residual counterexamples.
- `lake build`: PASS, 3471 jobs, with only pre-existing QR/Givens/FastMatMul
  linter warnings.
- `git diff --check`: PASS.
- Placeholder scan, `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/CompensatedSum.lean examples/LibraryLookup.lean`:
  PASS with no matches.
- `lake build LeanFpAnalysis.FP.Algorithms.CompensatedSum`: PASS after adding
  `finiteKahanStepTrace_zero_of_finiteSystem` and
  `finiteKahanStep_zero_of_finiteSystem`; PASS again after adding
  `finiteKahanPrefixState_one_of_finiteSystem`.
- `lake build LeanFpAnalysis.FP.Algorithms.CompensatedSum`: PASS after adding
  `kahanStepTrace_abstractCounterexample_zero`,
  `kahanStep_abstractCounterexample_zero_ne_exact`, and
  `not_forall_kahanStep_zero_exact`.
- `lake build LeanFpAnalysis.FP.Algorithms.CompensatedSum`: PASS after adding
  `kahanStepTrace_zero_of_exact_zero_path`,
  `kahanStep_zero_of_exact_zero_path`, and
  `kahanPrefixState_one_of_exact_zero_path`.
- `lake build LeanFpAnalysis.FP.Algorithms.CompensatedSum`: PASS after adding
  `kahanBiasedSmallCounterexampleFPModel`,
  `fl_kahanSum_biasedSmallCounterexample_twoStep`,
  `not_exists_fl_kahanSum_biasedSmallCounterexample_twoStep_source_bound_of_Cu_le_half`,
  and
  `not_forall_fl_kahanSum_backward_error_source_bound_bare_fpmodel_exactSubConstants`.
- `lake build LeanFpAnalysis.FP.Algorithms.CompensatedSum`: PASS after adding
  `kahanCoupledSourceCoeff_s_eq_returned_totalCorrectionPropagate`.
- `lake build LeanFpAnalysis.FP.Algorithms.CompensatedSum`: PASS after adding
  `kahanCoupledSourceCoeff_s_abs_sub_one_le_pairedCoeffMajorant_sum` and
  `kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_pairedCoeffMajorant_sum`.
- `lake env lean /private/tmp/higham_ch4_kahan_exact_start_axioms.lean`:
  PASS. Focused `#print axioms` for the three bare-model exact-start
  counterexample declarations, the biased small-`u` returned-cap
  route-elimination declarations, the three exact-zero-path bridge declarations,
  and `kahanCoupledSourceCoeff_s_eq_returned_totalCorrectionPropagate` reports
  only standard Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`.
