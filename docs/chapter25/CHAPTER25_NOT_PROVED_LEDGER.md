# Higham Chapter 25 Not-Proved Ledger

| Source item | Classification | Exact missing dependency | Evidence needed to close |
|---|---|---|---|
| Equation (25.11) and its implicit-function derivation | OPEN SELECTED / PARTIAL | The compiled limit theorem still consumes `Higham25ActualSolutionMapContract`, whose existence/uniqueness fields are the conclusion of the source's implicit-function step. There is no theorem from a sufficiently smooth residual `F` and nonsingular partial derivative `F_x` to a local solution map, nor a proof that its derivative is `-F_x⁻¹ F_d`. | A local implicit-function theorem instantiation for `isSolution dx dd := F (xStar + dx) (dStar + dd) = 0`, a neighborhood-restricted uniqueness contract, and the derivative identity. Then apply `higham25_eq25_11_of_actualSolutionMap_hasFDerivAt`. |
| Theorem 25.1 / (25.8) | DEFER-MISSING-PRECISE-STATEMENT | Undefined `≈` and “decreases until”; proof omitted | Precise quantifiers/constants/stopping index plus Tisseur §2.2 proof reconstruction. |
| Theorem 25.2 / (25.9) | DEFER-MISSING-PRECISE-STATEMENT | Same ambiguity for residual sequence; proof omitted | Precise endpoint plus Tisseur §2.3 proof reconstruction. |
| Rheinboldt `C(F,S)` and shrinking-set limit | DEFER-MISSING-PRECISE-STATEMENT | The printed max/min includes no distinct-point, compactness, positivity, or attainment hypotheses; “closed” is insufficient | A precise nonempty compact/nondegenerate domain statement and exact shrinking-set convergence semantics. |
| Rigorous residual/error factors `1/2`, `2` | DEFER-MISSING-PRECISE-STATEMENT | “Sufficiently close” and the required smoothness/Taylor hypotheses are omitted; proof is citation-only | Exact neighborhood and Taylor-remainder assumptions, followed by a reconstruction of Kelley Lemma 4.3.1. |

Problem 25.2 is explicitly a research problem and is excluded. Figure 25.1,
the `μ=10^8` experiment, notes, and Problem 25.1(c)'s practical explanation are
accounted-for exclusions rather than proof gaps.

Equation (25.11) is the chapter's open selected row, so the Chapter 25 gate is
**FAIL**. The smallest independent Taylor dependency is now proved:
`higham25_taylor_linear_bound_of_hasFDerivAt` derives the local first-order
bound from Fréchet differentiability, and
`higham25_eq25_11_of_actualSolutionMap_hasFDerivAt` carries it through the
literal feasible `sSup`. The remaining blocker is precisely the
source-facing implicit-function/derivative producer recorded in
`CHAPTER25_BOTTLENECK_LEDGER.md`; the other rows above remain stable source
deferrals.
