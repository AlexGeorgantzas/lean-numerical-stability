# Chapter 23 Not-Proved Ledger

The selected-scope gate is **FAIL**.

| Source row | Proved local substrate | Missing source object or proof | Status |
|---|---|---|---|
| (23.11), Miller | actual rounded conventional multiplication is proved separately | Miller's finite polynomial-algorithm theorem and the dimension constant `f_n` | OPEN |
| Theorem 23.2; (23.14)--(23.15) | exact one-level Strassen algebra; exact cost recurrence; scalar 12/46 error recurrence and closed coefficient | recursively rounded Strassen evaluator and the induction on its actual operations | OPEN |
| Theorem 23.3; (23.18) | exact one-level Winograd--Strassen algebra; scalar 18/89 recurrence and closed coefficient | recursively rounded Winograd--Strassen evaluator and induction | OPEN |
| Theorem 23.4; (23.19) | exact one-level bilinear evaluator; parameterized algebraic coefficient shape | cited Bini--Lotti theorem, its true `alpha`/`beta` construction, and rounded recursive bilinear evaluator | OPEN |
| 23.B3 / Problem 23.6 | `higham23ThreeMStrassenCoefficient` records the stated scalar modification | combined recursively rounded 3M--Strassen evaluator and error proof | OPEN |

Actual rounded evaluators do prove Theorem 23.1, (23.10), (23.17), and
(23.20)--(23.24), including explicit quadratic remainders and the relevant
`O(u²)` statement.

## Audit correction

The former `Higham23FirstOrderExpansion` endpoints did not arise from a
rounded recursive source evaluator.  Their witnesses manufactured a
polynomial computation with zero error, and support-count values were
presented as Bini--Lotti constants without the cited theorem.  Those
structures, producers, target theorems, and witnesses were removed.  Scalar
recurrence arithmetic is retained but is explicitly not counted as the
recursive error theorem.
