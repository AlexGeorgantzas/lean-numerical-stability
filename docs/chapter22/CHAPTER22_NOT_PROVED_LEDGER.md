# Chapter 22 Not-Proved Ledger

The selected-scope gate is **FAIL**.  The rows below are selected and
nonterminal; a proved substrate is recorded separately from the missing
source theorem.

| Source row | Proved local substrate | Missing source object or proof | Status |
|---|---|---|---|
| Table 22.1 V1--V6 | V7 is proved; the printed model formulas are documented | family-specific cited lower-bound/asymptotic proofs | OPEN |
| Algorithms 22.2--22.3; (22.15)--(22.17) | actual Stage-I and printed Stage-II recurrences; Stage-II Newton-to-basis synthesis; literal primal loop | Stage-I confluent interpolation invariant, finite `L_k`/`U_k` matrices tied to the loops, product `P⁻ᵀ`, and final dual/primal solve | OPEN |
| Theorem 22.4; (22.18)--(22.21) | exact algorithm definitions and scalar polynomial foundations | actual rounded operation graph, local factor perturbations, computed perturbed product, and Lemma 3.8 application | OPEN |
| Corollary 22.5; (22.22) | general exact algebra elsewhere in the module | displayed `n=3` factors, checkerboard signs for the named bases/nodes, and the no-cancellation specialization of Theorem 22.4 | OPEN |
| Theorem 22.6; (22.23)--(22.25) | the source assumption (22.24) is identified in the inventory | perturbed inverse factors produced from the actual algorithm and the conditional residual-product argument | OPEN |
| Corollary 22.7; Problem 22.8 | source coefficient and valid-range requirement are inventoried | Appendix upper-bidiagonal inverse-perturbation proof and its connection to the monomial factors | OPEN |
| Refinement consequence 22.B2 | `higham22RefinementError`, its closed form, and geometric convergence | instantiation of the Chapter 12 residual/refinement hypotheses for the actual Vandermonde solver | PARTIAL |

## Audit correction

The former positive-gap/asymptotic domains, solve-factor domains,
triangular-factor domains, first-order expansion domains, perturbation
domains, and identity/zero nonemptiness witnesses were removed.  Their
premises either selected an arbitrary object already satisfying the desired
estimate or directly contained the missing factorization/error expansion.
They therefore did not close the source rows.

The smallest genuine dependencies retained are
`higham22_eq22_15`, `higham22_eq22_16`,
`higham22_algorithm22_2StageII_correct`, and
`higham22_algorithm22_2_newton_invariant`.
