# Higham Chapter 25 Not-Proved Ledger

| Source item | Classification | Exact missing dependency | Evidence needed to close |
|---|---|---|---|
| Theorem 25.1 / (25.8) | DEFER-MISSING-PRECISE-STATEMENT | Undefined `≈` and “decreases until”; proof omitted | Precise quantifiers/constants/stopping index plus Tisseur §2.2 proof reconstruction. |
| Theorem 25.2 / (25.9) | DEFER-MISSING-PRECISE-STATEMENT | Same ambiguity for residual sequence; proof omitted | Precise endpoint plus Tisseur §2.3 proof reconstruction. |
| Rheinboldt `C(F,S)` and shrinking-set limit | DEFER-MISSING-PRECISE-STATEMENT | The printed max/min includes no distinct-point, compactness, positivity, or attainment hypotheses; “closed” is insufficient | A precise nonempty compact/nondegenerate domain statement and exact shrinking-set convergence semantics. |
| Rigorous residual/error factors `1/2`, `2` | DEFER-MISSING-PRECISE-STATEMENT | “Sufficiently close” and the required smoothness/Taylor hypotheses are omitted; proof is citation-only | Exact neighborhood and Taylor-remainder assumptions, followed by a reconstruction of Kelley Lemma 4.3.1. |
| Simple eigenvalue implies bordered-Jacobian nonsingularity | OPEN PRECISE PROSE | `Higham25SimpleEigenpairCertificate` supplies the left eigenvector/nonorthogonality and one-dimensional eigenspace facts used by the kernel proof, but no theorem constructs it from algebraic multiplicity one | A characteristic-polynomial/Jordan or generalized-eigenspace bridge from a standard simple-root predicate to the certificate. |

Problem 25.2 is explicitly a research problem and is excluded. Figure 25.1,
the `μ=10^8` experiment, notes, and Problem 25.1(c)'s practical explanation are
accounted-for exclusions rather than proof gaps.

The Chapter 25 gate is **FAIL**. Most of the formerly open precise eigenproblem
row is closed in `Higham25EigenClosure.lean`: the Jacobian, certificate-based
kernel triviality, and rounded `ψ` producer are proved. The source's bare
simple-eigenvalue hypothesis is not yet connected to that certificate. The
printed `2‖A‖` Lipschitz coefficient is formally false at `A=0`; the corrected
universal infinity-norm coefficient `2` is proved and the discrepancy is terminal.
Equation (25.11) is closed by `higham25_eq25_11_of_implicitFunction`, which
constructs the local unique solution map from the printed IFT hypotheses,
proves derivative `-F_x⁻¹ F_d`, and carries it through the literal feasible
`sSup`. The linear-system specialization and condition identity are also closed
by the `higham25_linearSystem_*` declarations. The Tisseur/Rheinboldt/Kelley
rows remain stable source deferrals and do not fail the gate.
