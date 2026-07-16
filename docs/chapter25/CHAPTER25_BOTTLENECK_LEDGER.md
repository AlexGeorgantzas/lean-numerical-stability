# Higham Chapter 25 Bottleneck Ledger

## Gate

The Chapter 25 core selected-scope gate is **FAIL**. The sole open selected
row recorded here is equation (25.11) together with the precise
implicit-function/Taylor prose on printed pp. 464-466 (PDFs 6-8).

## Equation (25.11)

| Field | Audit result |
|---|---|
| Printed hypotheses | `F(x*; d) = 0`, sufficient smoothness in `x` and `d`, and nonsingularity of `F_x`. |
| Printed construction | For sufficiently small `Δd`, the implicit-function theorem gives a unique `Δx`; Taylor expansion gives `Δx = -F_x⁻¹ F_d Δd + O(‖Δd‖²)`. |
| Printed conclusion | The literal shrinking-ball condition-number limit equals `‖F_x⁻¹ F_d‖ ‖d‖ / ‖x*‖`. |
| Closed locally | Literal feasible values and `sSup`; exact linearized supremum; nonvacuity; first-order left-inverse algebra; comparison of nonlinear and linearized suprema. |
| New closed dependency | `higham25_taylor_linear_bound_of_hasFDerivAt` derives `‖phi dd - L dd‖ ≤ c ‖dd‖` locally from `HasFDerivAt phi L 0`. `higham25_eq25_11_of_actualSolutionMap_hasFDerivAt` then proves the literal shrinking-ball limit, including the zero-data-norm edge. |
| Remaining target-bearing premise | `Higham25ActualSolutionMapContract` assumes existence and uniqueness of `phi` on the supplied domain. Those fields are the conclusion of the source's implicit-function step, not source hypotheses. |
| Missing derivative bridge | No theorem identifies the derivative of the produced solution map with the continuous linear map `-F_x⁻¹ ∘ F_d`. |
| Status | **OPEN SELECTED / PARTIAL**. A conditional theorem is useful, but it does not close the stronger printed row. |

## Smallest next source-facing theorem

The next closure theorem should start from a concrete residual
`F : X → D → Y`, a base point `(xStar, dStar)`, explicit differentiability
near that point, and a continuous-linear equivalence representing nonsingular
`F_x`. It should produce a radius and a neighborhood-restricted map `phi`
such that:

1. `F (xStar + phi dd) (dStar + dd) = 0` for sufficiently small `dd`;
2. every sufficiently small solution perturbation is `phi dd`;
3. `phi 0 = 0`; and
4. `HasFDerivAt phi (-F_x⁻¹.comp F_d) 0`.

That result can feed the already compiled
`higham25_eq25_11_of_actualSolutionMap_hasFDerivAt` after adapting the current
global solution-map contract to the local radius. Until this producer exists,
equation (25.11) must remain visible in the not-proved ledger.
