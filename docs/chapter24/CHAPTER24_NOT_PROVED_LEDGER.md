# Higham Chapter 24 Not-Proved Ledger

| Source item | Classification | Exact missing dependency | Evidence needed to close |
|---|---|---|---|
| Theorem 24.3 | OPEN / conditional transfer | All four rounded stages and their local perturbations now come from `higham24LiteralRoundedCirculantSolve`, but `Higham24MixedStabilityExecutionFamily` still assumes the final structured generator/RHS perturbation splits and first-order budgets | Derive `C(c+Δc)(x̂+Δx)=b+Δb` and the `eta log2(n) + 6u + O(u^2)` maximum-relative bound from the produced `Δ₁`, `Δ₂`, `E`, and `Δ₃`, including the inverse factors in (24.8). |
| Forward-error prose after Theorem 24.3 | DEFER-MISSING-PRECISE-STATEMENT | “A multiple of `kappa_2(C)u`” has no printed multiplier or quantified neighborhood | Select a precise sourced perturbation theorem before adding an endpoint. |

Problem 24.1 is an optional exercise and is excluded, not an unreported gap.
Figure 24.1 and §24.3 bibliography are also explicitly excluded.

Equations (24.6)-(24.7), both remaining rounded solver stages, the composed
literal four-stage execution, and the quantitative backward-stability
consequence are closed by actual producers. Theorem 24.3 remains selected;
conditional certificates and exact-zero witnesses are retained only as
intermediate infrastructure.
