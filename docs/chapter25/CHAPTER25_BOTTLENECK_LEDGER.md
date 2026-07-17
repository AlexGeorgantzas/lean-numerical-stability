# Higham Chapter 25 Bottleneck Ledger

## Gate

The Chapter 25 core selected-scope gate is **PASS**. The former bottleneck,
equation (25.11) together with the implicit-function/Taylor prose on printed
pp. 464-466 (PDFs 6-8), is closed.

## Equation (25.11)

| Field | Audit result |
|---|---|
| Printed hypotheses | `F(x*; d) = 0`, sufficient smoothness in `x` and `d`, and nonsingularity of `F_x`. |
| Printed construction | For sufficiently small `Δd`, the implicit-function theorem gives a unique `Δx`; Taylor expansion gives `Δx = -F_x⁻¹ F_d Δd + O(‖Δd‖²)`. |
| Printed conclusion | The literal shrinking-ball condition-number limit equals `‖F_x⁻¹ F_d‖ ‖d‖ / ‖x*‖`. |
| IFT hypotheses | `higham25_isContDiffImplicitAt_of_partialEquiv` proves Mathlib's `IsContDiffImplicitAt` from the split Fréchet derivative, `C¹` regularity, and a continuous-linear equivalence representing nonsingular `F_x`. |
| Local solution producer | `higham25_implicitFunction_local_solution_contract` produces data and solution neighborhoods, the base value, local solvability, and local uniqueness. |
| Derivative bridge | `higham25_implicitFunction_hasFDerivAt` differentiates `F(d,phi d)=F(0,0)` and proves `D phi(0) = -F_x⁻¹ F_d`. |
| Shrinking-ball bridge | `higham25_eventually_closedBall_subset_of_mem_nhds` and `higham25_actualConditionValues_eq_localSolutionGraph` show the literal feasible set eventually equals the local solution graph. |
| Source-facing endpoint | `higham25_eq25_11_of_implicitFunction` produces the local map and proves the exact literal epsilon-indexed `sSup` limit from the printed hypotheses. |
| Hidden-hypothesis result | No existence, uniqueness, derivative identity, Taylor remainder, or condition-number conclusion is assumed. The assumptions are source data: base residual zero, `C¹` regularity, the split derivative, nonnegative data norm, positive solution norm, and invertibility of `F_x`. |
| Status | **CLOSED / PASS**. |

## Remaining non-selected rows

Theorem 25.1/(25.8), Theorem 25.2/(25.9), Rheinboldt's under-specified
max/min quotient, and the cited local residual/error constants remain stable
`DEFER-MISSING-PRECISE-STATEMENT` rows. They are recorded in the not-proved
ledger and do not fail the selected-scope gate.
