# Chapter 22 Proof-Source Ledger

| Selected claim | Source location | What the source proves/assumes | Local route | Status |
|---|---|---|---|---|
| Vandermonde nonsingularity | p. 416 | distinct nodes iff nonsingular | Mathlib Vandermonde determinant adapter | PROVED: `higham22_vandermonde_det_ne_zero_iff` |
| Algorithm 22.1 | pp. 416--417 | master polynomial and synthetic division form `V⁻¹` | actual quotient rows, cardinality, left inverse | PROVED |
| (22.2)--(22.3) | pp. 416--418 | inverse entries and two-sided infinity-norm bound | Vieta/Mahler and finite-product lemmas | PROVED |
| General confluent nonsingularity | p. 418 | distinct nonconfluent nodes give a nonsingular transpose | Hermite uniqueness via multiplicities | PROVED |
| Table 22.1 V1--V6 | p. 418, cited literature | six family-specific estimates | external proof must be imported or reconstructed for the actual node families | OPEN |
| Table 22.1 V7 | p. 418 | roots-of-unity condition number is one | Fourier/Vandermonde inverse | PROVED |
| (22.6)--(22.14) and Stage II | pp. 419--421 | recurrence-basis and nested-polynomial derivation | sparse basis multiplication and Newton synthesis | PROVED through `higham22_algorithm22_2StageII_correct` |
| Algorithms 22.2--22.3; (22.15)--(22.17) | pp. 421--423 | literal loops yield triangular factors whose product is `P⁻ᵀ` | actual state recurrences exist; matrix factors and Stage-I interpolation invariant do not | PARTIAL / OPEN |
| Theorem 22.4; (22.18)--(22.21) | p. 424 | rounded Stage-I/II perturbations produce the forward bound | requires rounded loop evaluator and operation-level factor perturbation proof | OPEN |
| Corollary 22.5; (22.22) | pp. 424--425 | checkerboard signs remove cancellation | requires the actual displayed factors and named basis/node sign argument | OPEN |
| Theorem 22.6; (22.23)--(22.25) | pp. 425--426 | conditional residual bound under (22.24) | retain (22.24) as an explicit source assumption, then analyze actual inverse factors | OPEN |
| Corollary 22.7; Problem 22.8 | pp. 426, 431 | monomial specialization from an upper-bidiagonal inverse perturbation | formalize Appendix proof for the actual factor | OPEN |
| Algorithm 22.8 / Problem 22.10 | p. 427 and Appendix route | extended Clenshaw recurrence returns derivatives | actual normalized-jet loop and Taylor/factorial invariant | PROVED |
| Refinement prose 22.B2 | p. 428, Theorem 12.3 cross-reference | Vandermonde refinement becomes asymptotically componentwise stable | scalar contraction proved; solver-specific hypotheses not instantiated | PARTIAL |

The proof source was the rendered local PDF
`References/1.9780898718027.ch22.pdf`, especially pp. 422, 424--426,
together with installed Mathlib.  No target-equivalent premise or synthetic
nonempty witness is counted as a proof source.
