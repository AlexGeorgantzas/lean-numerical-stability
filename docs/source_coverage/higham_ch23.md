# Higham Chapter 23 Source Coverage

| Source | Lean surface | Status |
|---|---|---|
| (23.1) conventional multiplication | repository matrix multiplication | reused |
| (23.2) Winograd identity | `higham23_eq23_2_winograd_identity` | proved exact arithmetic |
| (23.10), (23.17) conventional error | actual rounded matrix evaluator, componentwise exact-gamma/first-order theorem, max-entry norm envelope | proved with explicit quadratic remainder and formal `O(u²)` coefficient theorem |
| (23.3)--(23.4) Strassen | `Higham23Block2`, `higham23Strassen2`, correctness theorem | proved exact algorithm |
| (23.5) Strassen costs | `higham23StrassenCosts`, multiplication/addition recurrence solutions, `higham23_eq23_5_strassen_costs` | proved exact source closed forms from executable cost recursion |
| (23.6) Winograd--Strassen | `higham23WinogradStrassen2`, correctness theorem | proved exact algorithm |
| (23.7a)--(23.7b) | `Higham23BilinearAlgorithm`, `higham23BilinearProduct`, `higham23BilinearEvaluate`, correctness surface | proved exact one-level evaluator |
| (23.8)--(23.9) 3M | `higham23ThreeM`, correctness theorem | proved exact algorithm |
| (23.20)--(23.22), diagonal scaling | actual conventional/3M rounded entry evaluators, exact-gamma bounds, explicit quadratic remainder with `O(u²)` theorem, and diagonal budget scaling theorem | proved componentwise first-order paths and scaling invariance |
| (23.16), recurrence after (23.18) | canonical coefficient functions, source-facing recurrence steps, and displayed closed-coefficient upper bounds | proved exact arithmetic, no supplied recurrence certificate needed |
| Theorem 23.1/(23.12) and balanced scaling | `higham23FlWinogradInnerProduct`, source-shaped factor expansion, `higham23_theorem23_1_winograd_error`, `higham23_balanced_winograd_error` | proved for the actual rounded pair-transform/dot/subtraction path |
| (23.23)--(23.24) | actual rounded conventional/3M imaginary matrices, complex induced infinity norm, sharp `sqrt 2` row-budget lemma | proved exact-gamma normwise bounds with source constants 2 and 4 |
| (23.11) Miller generic polynomial bound | `Higham23FirstOrderExpansion`, constructive producer/nonzero witness, named consequence | PASS (EXPLICIT-DOMAIN) |
| Theorem 23.2 / (23.14)--(23.16) | canonical Strassen coefficient, solved closed form, named expansion-domain theorem and producer | PASS (EXPLICIT-DOMAIN) |
| Theorem 23.3 / (23.18) | canonical Winograd--Strassen coefficient, solved closed form, named expansion-domain theorem and producer | PASS (EXPLICIT-DOMAIN) |
| Theorem 23.4 / (23.19) | tensor support count, positive support-dependent constants, Bini--Lotti coefficient, named theorem and producer | PASS (EXPLICIT-DOMAIN) |
| 23.B3 / Problem 23.6 | combined 3M--Strassen coefficient, named theorem and producer | PASS (EXPLICIT-DOMAIN) |

Full decisions and every equation/Problem/Appendix row are in `docs/chapter23/CHAPTER23_SOURCE_INVENTORY.md`.
