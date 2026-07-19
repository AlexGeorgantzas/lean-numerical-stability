# Chapter 22 Proof-Source Ledger

| Selected claim | Source location | Local proof route | Status |
|---|---|---|---|
| Vandermonde algebra, (22.1)--(22.4), Algorithm 22.1 | pp. 416--418 | Lagrange/Vieta, synthetic quotient, determinant adapters | PROVED |
| Table 22.1 V1--V6 | p. 418 | literature-summary rows occurring only in the visual table | SKIP-FIGURE-TABLE in core mode |
| Table 22.1 V7 and Table 22.2 | pp. 418, 422 | Fourier inverse and five recurrence families | PROVED |
| (22.5)--(22.17), Algorithm 22.2 | pp. 419--422 | contiguous repeated-node divided differences, Newton synthesis, literal finite factors, Hermite uniqueness | PROVED |
| Algorithm 22.3 | pp. 422--423 | literal Stage-I upper-transpose loop, repeated-node `xlast` adjoint invariant for Stage II, executor-to-factor bridge, primal solve | PROVED for the separate printed executor |
| (22.19)--(22.21), Theorem 22.4, (22.18) | p. 424 | primitive rounded graph, actual lower/upper perturbation producers, complex Lemma 3.8 | PROVED |
| (22.22), Corollary 22.5 | pp. 424--425 | general lower/upper checkerboard factors and named monomial/Chebyshev/Legendre/Hermite specialization | PROVED |
| (22.23)--(22.25), Theorem 22.6 | pp. 425--426 | reversed actual inverse factors, source assumption `Higham22Eq22_24`, lower inverse producer, complex Lemma 3.8, actual residual identity | PROVED, conditional exactly as source on (22.24) |
| Problem 22.8 / Corollary 22.7 | pp. 426, 431 | complex upper-bidiagonal inverse formula, exact coefficient, neutral-operation exactness, actual rounded-factor identification, recursive sequence lift, and closed residual composition | PROVED |
| Algorithm 22.8 / Problem 22.10 | p. 427 | normalized Taylor/Clenshaw jet invariant | PROVED |
| Refinement prose 22.B2 | p. 428 | no explicit stability predicate/constant/threshold/quantified endpoint; optional Chapter 5 and Chapter 12 bridges are retained | DEFER-MISSING-PRECISE-STATEMENT |

Equation (22.24) is the only simplifying numerical assumption introduced by
the *general* Chapter 22 residual theorem, exactly matching the book.  For
Corollary 22.7, `higham22Closure_eq22_24_monomial` is the independent producer
promised by Problem 22.8.  No premise containing the target inverse bound or
final residual conclusion is counted as closure.
