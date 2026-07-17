# Higham Chapter 22 Source Coverage

- Source: `References/1.9780898718027.ch22.pdf`, printed pp. 415--431.
- Core status: **PASS**.
- Exhaustive row inventory: `docs/chapter22/CHAPTER22_SOURCE_INVENTORY.md`.

| Source | Status and Lean surface |
|---|---|
| Vandermonde definition, Algorithm 22.1, (22.1)--(22.4) | PROVED end to end |
| Table 22.1 V1--V6 | SKIP-LITERATURE-SUMMARY; external citation table |
| Table 22.1 V7 and Table 22.2 | PROVED |
| (22.5)--(22.17), Algorithm 22.2 | PROVED; repeated-node Hermite factorization and final solve |
| Algorithm 22.3 | PROVED for the separate printed natural-indexed executor via `higham22_algorithm22_3_eq_factorized`, with literal primal solve `higham22Hermite_algorithm22_3_solve` |
| (22.18)--(22.21), Theorem 22.4 | PROVED from the actual primitive rounded graph |
| (22.22), Corollary 22.5 | PROVED for all four named source bases |
| (22.23)--(22.25), Theorem 22.6 | PROVED conditional exactly on source assumption (22.24) |
| Problem 22.8, Corollary 22.7 | PROVED structured inverse coefficient, monomial residual specialization, and `n(n+4)` first derivative |
| Algorithm 22.8 / Problem 22.10 | PROVED |
| Refinement consequence 22.B2 | REUSED from proved Chapter 12 Theorem 12.3 via bridge `ch22b_refinement_converges_via_ch12` (`LeanFpAnalysis/FP/Algorithms/Vandermonde/Higham22Ch12RefinementBridge.lean`): the actual refinement residual's per-step contraction is produced by applying `higham12_3_exact_one_step_residual_bound`, and convergence closes through the local `higham22_refinement_converges` |

The source assumption (22.24) is represented by `Higham22Eq22_24`; no final
error or residual conclusion is assumed.  The forward and residual endpoints
operate on factors extracted from the actual rounded Algorithm 22.2 graph.
