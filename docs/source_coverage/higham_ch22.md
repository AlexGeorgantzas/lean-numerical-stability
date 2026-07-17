# Higham Chapter 22 Source Coverage

| Source | Lean surface | Status |
|---|---|---|
| Vandermonde definition/nonsingularity; (22.1)--(22.3) | Vandermonde, Lagrange/Vieta, inverse-norm theorems | PROVED |
| Algorithm 22.1 | actual master polynomial and synthetic division | PROVED end-to-end exact path |
| Confluent example/general nonsingularity | displayed and arbitrary-multiplicity models | PROVED |
| Table 22.1 V1--V6 | no source-family theorem | OPEN; cited estimates |
| Table 22.1 V7; Table 22.2 | root-unity inverse and five polynomial families | PROVED |
| (22.6)--(22.14) | recurrence, Newton form, sparse Stage-II synthesis | PROVED |
| Algorithms 22.2--22.3; (22.15)--(22.17) | actual loop recurrences and Stage-II invariant | PARTIAL; factor product and final solves OPEN |
| Theorem 22.4; (22.18)--(22.21) | no rounded loop-derived perturbation theorem | OPEN |
| Corollary 22.5; (22.22) | no actual checkerboard factor specialization | OPEN |
| Theorem 22.6; (22.23)--(22.25) | source assumption identified; no algorithmic residual proof | OPEN |
| Corollary 22.7; Problem 22.8 | Appendix dependency inventoried | OPEN |
| Algorithm 22.8 / Problem 22.10 | derivative Clenshaw loop and invariants | PROVED |
| Refinement consequence 22.B2 | scalar contraction recurrence | PARTIAL; solver instantiation OPEN |

The exhaustive row inventory is
`docs/chapter22/CHAPTER22_SOURCE_INVENTORY.md`.  The selected-scope gate is
**FAIL**; removed target-bearing domains and synthetic witnesses are not
counted as coverage.
