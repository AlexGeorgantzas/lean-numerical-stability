# Higham Chapter 22 Source Coverage

| Source | Lean surface | Status |
|---|---|---|
| Vandermonde definition/nonsingularity | `higham22Vandermonde`, `higham22_vandermonde_det_ne_zero_iff` | proved |
| (22.1)--(22.2) cardinal interpolation and inverse entries | `higham22LagrangeValue`, `higham22_lagrangeValue_node`, `higham22_eq22_2_inverse_entry` | proved, including the elementary-symmetric coefficient identity |
| Algorithm 22.1 | `higham22Algorithm1MasterPolynomial`, `higham22Algorithm1SyntheticQuotient`, `higham22Algorithm1Printed`, correctness/equality theorems | proved exact printed master-product and synthetic-division path; floating-point error analysis is not claimed by this exact algorithm |
| (22.3) inverse infinity-norm bounds | `higham22_eq22_3` plus rowwise Mahler/Vieta estimates | proved exact two-sided finite-product bound |
| symbolic confluent example (22.4) | `higham22ConfluentExample`, determinant and transpose nonsingularity theorems | proved for the displayed multiplicity-`3,2` family; general closure is listed below |
| general confluent nonsingularity prose | `Higham22ConfluentSlot`, `higham22ConfluentVandermonde`, Hermite uniqueness/injectivity/determinant theorems | proved for arbitrary finite multiplicities and distinct nodes |
| (22.6a)--(22.7) | `Higham22ThreeTermRecurrence`, `higham22Psi` | proved exact contracts |
| Table 22.2 recurrence parameters | `higham22PolynomialSequence`; five `higham22_table22_2_*` row theorems; theta-nonzero and Legendre-normalization theorems | proved |
| Table 22.1 (V7) | `higham22RootUnityInverse`, left-inverse theorem, `higham22_table22_1_V7_kappa2` | proved roots-of-unity Euclidean condition product equals one |
| (22.10)--(22.11) | `higham22NewtonNest` | proved exact recurrence substrate |
| Algorithm 22.8 / Problem 22.10 recurrence | `higham22Algorithm22_8`, jet/Taylor and scalar Clenshaw invariants | proved actual normalized derivative-state loop and final factorial scaling |
| Table 22.1 (V1)--(V6) | exact printed model functions, positive-gap/relative-error domains, row theorems and concrete producers | PASS (EXPLICIT-DOMAIN) for citation-only rows |
| (22.15)--(22.17) | actual stage recurrences, transpose adapter, triangular factor domain and witness | state recurrences proved; finite factor statement PASS (EXPLICIT-DOMAIN) |
| Algorithms 22.2, 22.3 | actual Stage-I scan, printed dual Stage II, sparse synthesis invariant, literal primal loop, operator-factor solve theorems | executable paths proved; solve conclusions PASS (EXPLICIT-DOMAIN) with producer/witness |
| Theorem 22.4 / (22.18)--(22.21) | factor perturbation and vector expansion domains, ordered product, named theorem and producers | PASS (EXPLICIT-DOMAIN), leading `7nu` plus explicit quadratic remainder |
| (22.22) / Corollary 22.5 | no-cancellation term domain and cancellation-free theorem | PASS (EXPLICIT-DOMAIN) |
| (22.23)--(22.25) / Theorem 22.6 | inverse factor apply, explicit source assumption (22.24), named conditional residual theorem | PASS (EXPLICIT-DOMAIN); assumption remains visible |
| Corollary 22.7 / Problem 22.8 | printed bidiagonal coefficient, valid-range producer, monomial residual theorem | PASS (EXPLICIT-DOMAIN) with explicit quadratic remainder |
| refinement consequence 22.B2 | exact contraction recurrence and `higham22_refinement_converges` | proved |

Full decisions and every equation/Problem/Appendix row are in `docs/chapter22/CHAPTER22_SOURCE_INVENTORY.md`.
