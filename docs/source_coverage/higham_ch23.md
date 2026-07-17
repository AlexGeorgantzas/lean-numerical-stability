# Higham Chapter 23 Source Coverage

| Source | Lean surface | Status |
|---|---|---|
| (23.1)--(23.2) | conventional multiplication; Winograd identity | REUSED / PROVED |
| (23.3)--(23.4) | exact block model and Strassen evaluator | PROVED |
| (23.5) | executable cost recurrence and closed forms | PROVED |
| (23.6) | exact Winograd--Strassen evaluator | PROVED |
| (23.7a)--(23.7b) | exact one-level bilinear evaluator | PROVED |
| (23.8)--(23.9) | exact 3M identity | PROVED |
| (23.10), (23.17) | actual rounded conventional matrix evaluator | PROVED with quadratic remainder |
| (23.11) | literal rounded finite bilinear circuit; explicit algorithm-dependent `f_n` | PROVED with `O(u²)` remainder |
| Theorem 23.1 / (23.12) | actual rounded Winograd inner product | PROVED |
| Theorem 23.2 / (23.14)--(23.16) | literal recursive rounded Strassen evaluator, exact nonlinear induction, closed 12/46 coefficient, explicit remainder | PROVED; remainder is `O(u²)` |
| Theorem 23.3 / (23.18) | literal 15-addition recursive Winograd--Strassen evaluator and 18/89 induction | PROVED; remainder is `O(u²)` |
| Theorem 23.4 / (23.19) | literal recursive bilinear evaluator; explicit tensor-dependent `alpha`,`beta` | PROVED; remainder is `O(u²)` |
| (23.20)--(23.24), scaling | actual rounded conventional/3M complex paths | PROVED |
| 23.B3 / Problem 23.6 | literal rounded input sums, three recursive Strassen products, and rounded 3M outputs | PROVED with source `6*(c+4)` coefficient and `O(u²)` remainders |

The exhaustive row inventory is
`docs/chapter23/CHAPTER23_SOURCE_INVENTORY.md`.  The selected-scope gate is
**PASS**; all selected rows are backed by actual rounded evaluators rather
than synthetic target-bearing expansion witnesses.
