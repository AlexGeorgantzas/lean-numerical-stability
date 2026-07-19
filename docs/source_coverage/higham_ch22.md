# Higham Chapter 22 Source Coverage

- Source: `References/1.9780898718027.ch22.pdf`, printed pp. 415--431.
- Core status: **PASS (fresh strict re-audit)**.
- Exhaustive row inventory: `docs/chapter22/CHAPTER22_SOURCE_INVENTORY.md`.

| Source | Status and Lean surface |
|---|---|
| Vandermonde definition, Algorithm 22.1, (22.1)--(22.4) | PROVED end to end |
| Table 22.1 V1--V6 | SKIP-FIGURE-TABLE in core mode: these are literature-summary rows whose only source occurrence is the visual table; V7 remains a useful independently formalized extra |
| Table 22.1 V7 and Table 22.2 | PROVED |
| (22.5)--(22.17), Algorithm 22.2 | PROVED; repeated-node Hermite factorization and final solve |
| Algorithm 22.3 | PROVED for the separate printed natural-indexed executor via `higham22_algorithm22_3_eq_factorized`, with literal primal solve `higham22Hermite_algorithm22_3_solve` |
| (22.18)--(22.21), Theorem 22.4 | PROVED from the actual primitive rounded graph |
| (22.22), Corollary 22.5 | PROVED for all four named source bases |
| (22.23)--(22.25), Theorem 22.6 | PROVED conditional exactly on the source's general simplifying assumption (22.24) |
| Problem 22.8, Corollary 22.7 | PROVED: `higham22Closure_eq22_24_monomial` identifies every actual state-dependent rounded monomial Stage-II factor with the structured complex bidiagonal perturbation, proves nonsingularity and the inverse-entry coefficient, and `higham22_corollary22_7_monomial_residual_closed` supplies the source-facing residual endpoint without a target-bearing premise |
| Algorithm 22.8 / Problem 22.10 | PROVED |
| Refinement consequence 22.B2 | DEFER-MISSING-PRECISE-STATEMENT: the prose gives no explicit stability predicate, constant, threshold, or quantified asymptotic endpoint; the existing Chapter 5 residual and Chapter 12 envelope bridges remain honest optional strengthening |

The source's *general* simplifying assumption (22.24) is represented by
`Higham22Eq22_24`, which is appropriate for conditional Theorem 22.6.  For
monomials, the new closure module derives that assumption from the actual
primitive rounded execution and Problem 22.8.  Table 22.1 remains a visual
literature-summary artifact under the core-mode figure/table rule, while the
unquantified refinement sentence is deferred rather than promoted into an
invented theorem.  All selected Chapter 22 obligations are therefore closed.
