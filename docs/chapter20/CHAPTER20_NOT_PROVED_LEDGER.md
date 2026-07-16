# Chapter 20 Not-Proved Ledger

## Gate

The Chapter 20 modular selected-scope gate is **PASS** as of 2026-07-16.
All 12 named results pass at their documented APIs, and every selected numbered
equation is closed or explicitly deferred. There are **no Chapter 20-owned
selected blockers**.

The authoritative row-by-row classifications are in
`docs/chapter20/CHAPTER20_SOURCE_INVENTORY.md`. The source-strengthening rows
below are kept so that literal-trace closure is not mistaken for the sharper
constants and row-local scales printed in the cited upstream analyses.

## Upstream source-strengthening dependencies

| Interface | Chapter 20 closure already proved | Remaining source strengthening |
|---|---|---|
| Theorem 20.7 / Cox--Higham pivoted QR | `PivotedStoredQRSplit3BNumericalContract` contains only three numerical facts for the literal traces: the pivot-position QR residual bound, source-row RHS bound, and transported triangular-correction bound. It has no minimizer, returned-vector, or final backward-error field. `fl_pivotedStoredQR_returnedX_exactMinimizer_of_split3B` consumes that contract and runs the literal `fl_backSub` assembly. `Higham20Theorem20_7Runtime.lean` fully instantiates the contract without a row-policy or component-budget premise: `pivotedStoredQR_split3B_numericalContract_runtime` bounds the two accumulated residuals by finite sums of local `Eseq` norms and bounds `Q[DeltaR;0]` by the final top-`R` column scale. `fl_pivotedStoredQR_returnedX_exactMinimizer_of_runtime` is the direct literal QR/RHS/back-substitution endpoint on the visible `n > 0`, gamma-valid, nonzero-top-diagonal domain. This is an execution-derived exact-Real runtime certificate, not a Lean-executability claim. | The runtime scales are conservative and row-uniform; they are not the printed Cox--Higham source-row compression. `pivotedStoredQR_split3B_numericalContract_of_coxHigham` and `fl_pivotedStoredQR_returnedX_exactMinimizer_of_coxHigham` provide that stronger form only under explicit forward row-policy and local component-budget hypotheses. Optional `PivotedStoredQRCoxHighamRowSortingCaps` recover the printed initial-row scale. Thus the literal computation has a no-placeholder producer, while the sharper printed `alpha`/`beta`/`phi` constants remain a conditional upstream/source-strengthening result. |
| MGS stability sentence / Problem 20.5 | `Higham19Alg12MGSRounded.lean` defines the literal rounded Algorithm 19.12 loop, telescopes its local errors into `mgsRoundedProductEntryBudget`, and proves the polar-resolvent repair `toGlobalRepairWithAccumulatedPolarBudget`. `Higham19Alg12MGSRepair.lean` adds the non-circular computed-Gram compression `toGlobalRepairWithLocalGramBudget`, whose numerator is the local trace budget plus `(gramCoeff * u) * ||Rhat(:,j)||₂`. `Problem20_5.actualAugmentedMGSBackSub_end_to_end_accumulatedPolar` and `_localGram` run the actual `[A b]` loop and `fl_backSub` and construct the nearby exact least-squares problem. | The accumulated-polar endpoint has no external repair premise on its explicit tall/full-pivot/positive-column and gamma-valid domain. The computed-Gram endpoint instead assumes the visible runtime inequality `||I-QhatᵀQhat||_F <= gramCoeff*u`. What remains upstream is Higham Theorem 19.13's stronger, condition-number-independent printed `c3*u` column bound (the padded-Householder/QR-sensitivity route), not the existence of a concrete literal-MGS global repair or the Chapter 20 transfer. |

## Closed former queue rows

- The p. 385 zero-`Delta b` row is **PASS (EXPLICIT-DOMAIN)**.
  `metricGraphSmallness_of_frobNorm_le` derives every former
  `MetricGraphSmallness` field from the source-sized Frobenius perturbation
  bound together with
  `rhsRadius fp m n < 1` and
  `metricDefectEnvelope fp m n < 1`.
  `householder_qr_fl_backSub_matrix_only_backward_error_all_rhs_of_scalar_smallness`
  then proves the literal-computation matrix-only result for every RHS.
- Theorem 20.7 is **PASS (CH20 ASSEMBLY / LITERAL RUNTIME PRODUCER;
  EXPLICIT-DOMAIN; SOURCE-COORDINATE CORRECTION)**. The legacy strict
  cross-stage scale premise is not silently retained:
  `sigmaHistory_not_forall_literal_rounded_trace` gives a literal rounded-trace
  counterexample. Likewise,
  `pivotPositionFactor_not_le_sourceColumnFactor_forall` refutes relabeling a
  pivot-position `j^2` factor as an original source-column `j^2` factor.
  Corrected endpoints retain `j^2` in pivot-position coordinates and use the
  proved uniform `n^2` envelope in source coordinates.
  `fl_pivotedStoredQR_returnedX_exactMinimizer_of_runtime` now supplies the
  complete literal execution with conservative local-`Eseq`/top-`R` scales and
  no Cox--Higham row-policy or component-budget premise.
- Problem 20.5 is **PASS (LITERAL END-TO-END ACCUMULATED-POLAR;
  COMPUTED-GRAM EXPLICIT-DOMAIN)**. The actual augmented MGS and
  back-substitution return now construct their global polar repair and nearby
  exact least-squares problem. The stronger printed condition-independent
  `c3*u` column coefficient remains upstream Theorem 19.13 work.
- Theorem 20.8 / (20.25), (20.13a/b), (20.16), (20.26), the alternative
  Theorem 20.2 bound, Problem 20.3, the actual rounded cross-product example,
  the sharp p. 385 residual-quality estimate, and the constructed p. 399
  elimination method have source-facing endpoints.
- The p. 402 equal-rank Wedin extension is not an open proof obligation: a
  checked rational counterexample shows that the printed extension is false
  as stated, so it is classified **PASS / SOURCE DISCREPANCY**.

Equation (20.14), the rough corrected-seminormal forward bound, empirical
tables, machine-specific output, literature notes, and optional Problems not
selected in core mode remain deferred or excluded. They are not proof failures.

## Rejected closure shortcuts

- A bare Split 3B contract counts only at its documented modular boundary.
  The runtime producer is now connected for the literal computation, but its
  row-uniform trace scales must not be relabeled as the printed Cox--Higham
  source-row `alpha`/`beta` compression.
- The Theorem 20.7 contract is acceptable because it contains no
  least-squares minimizer, returned solution, or final theorem conclusion.
- The false strict rounded sigma history and false source-index `j^2`
  translation are recorded by formal counterexamples rather than assumed.
- `FPModel.exactWithUnitRoundoff` does not prove a theorem about the rounded
  source algorithm.
- `ModifiedGramSchmidtGlobalRepair` remains an honest numerical repair
  interface; it does not contain the Chapter 20 minimizer or returned-vector
  conclusion. The literal loop now constructs it with an accumulated-polar
  coefficient, and the computed-Gram adapter assumes only a directly stated
  Gram-defect bound, not the desired repair conclusion.
- The false p. 402 Wedin sentence is recorded by counterexample rather than
  weakened, silently strengthened, or retained as an impossible work item.
