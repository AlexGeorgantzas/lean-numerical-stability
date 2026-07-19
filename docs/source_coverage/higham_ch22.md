# Higham Chapter 22 Source Coverage

- Source: `References/1.9780898718027.ch22.pdf`, printed pp. 415--431.
- Core status: **FAIL (strict re-audit)**.
- Exhaustive row inventory: `docs/chapter22/CHAPTER22_SOURCE_INVENTORY.md`.

| Source | Status and Lean surface |
|---|---|
| Vandermonde definition, Algorithm 22.1, (22.1)--(22.4) | PROVED end to end |
| Table 22.1 V1--V6 | OPEN; these are precise inequalities/asymptotics and cannot be skipped merely because the table cites external papers |
| Table 22.1 V7 and Table 22.2 | PROVED |
| (22.5)--(22.17), Algorithm 22.2 | PROVED; repeated-node Hermite factorization and final solve |
| Algorithm 22.3 | PROVED for the separate printed natural-indexed executor via `higham22_algorithm22_3_eq_factorized`, with literal primal solve `higham22Hermite_algorithm22_3_solve` |
| (22.18)--(22.21), Theorem 22.4 | PROVED from the actual primitive rounded graph |
| (22.22), Corollary 22.5 | PROVED for all four named source bases |
| (22.23)--(22.25), Theorem 22.6 | PROVED conditional exactly on the source's general simplifying assumption (22.24) |
| Problem 22.8, Corollary 22.7 | PARTIAL: the abstract structured-bidiagonal coefficient and `n(n+4)` derivative are proved, but the actual monomial rounded Stage-II factor sequence has not been connected to that structure; `higham22_corollary22_7_monomial_residual` still takes its target `Higham22Eq22_24` specialization as a premise |
| Algorithm 22.8 / Problem 22.10 | PROVED |
| Refinement consequence 22.B2 | PARTIAL: `ch22b_horner_residual_error_via_higham5_3` and `ch22b_horner_derivative_error_via_higham5_7` now provide the genuine Chapter 5 -> residual-accuracy edge, and Chapter 12 gives the one-step envelope; the separate geometric contraction remains an explicit premise of `ch22b_refinement_converges_via_ch12`, so the printed asymptotic componentwise backward-stability conclusion is not yet produced |

The source's *general* simplifying assumption (22.24) is represented by
`Higham22Eq22_24`, which is appropriate for conditional Theorem 22.6.  The
book's Corollary 22.7, however, says that Problem 22.8 discharges that premise
for monomials.  The current Lean corollary does not yet do so.  This producer
gap, the precise Table 22.1 rows V1--V6, and the final refinement-stability
endpoint keep the chapter open under the strict core policy.
