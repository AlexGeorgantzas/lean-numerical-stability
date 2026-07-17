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
| (23.11) | no actual Miller theorem | OPEN |
| Theorem 23.1 / (23.12) | actual rounded Winograd inner product | PROVED |
| Theorem 23.2 / (23.14)--(23.16) | scalar 12/46 recurrence and closed coefficient | PARTIAL; recursive rounded theorem OPEN |
| Theorem 23.3 / (23.18) | scalar 18/89 recurrence and closed coefficient | PARTIAL; recursive rounded theorem OPEN |
| Theorem 23.4 / (23.19) | parameterized coefficient shape only | OPEN |
| (23.20)--(23.24), scaling | actual rounded conventional/3M complex paths | PROVED |
| 23.B3 / Problem 23.6 | scalar combined coefficient only | PARTIAL; error theorem OPEN |

The exhaustive row inventory is
`docs/chapter23/CHAPTER23_SOURCE_INVENTORY.md`.  The selected-scope gate is
**FAIL**; removed synthetic expansion domains and witnesses are not counted
as coverage.
