# Higham Chapter 24 Not-Proved Ledger

| Source item | Classification | Exact missing dependency | Evidence needed to close |
|---|---|---|---|
| Forward-error prose after Theorem 24.3 | DEFER-MISSING-PRECISE-STATEMENT | “A multiple of `kappa_2(C)u`” has no printed multiplier or quantified neighborhood | Select a precise sourced perturbation theorem before adding an endpoint. |

Theorem 24.3 is closed for the literal four-stage rounded solver by
`higham24_theorem24_3_literal_firstOrder` and
`higham24_theorem24_3_literal_quadraticRemainder`.  The generator, right-hand
side, and solution perturbations are constructed from the produced
`Δ₁`, `Δ₂`, `E`, and `Δ₃`; the exact structured equation is proved, and the
printed `t*eta + 6u + O(u²)` radius has an explicit quadratic coefficient
under the standard `mu ≤ cMu*u` small-error regime.

Problem 24.1 is an optional exercise and is excluded, not an unreported gap.
Figure 24.1 and §24.3 bibliography are also explicitly excluded.
