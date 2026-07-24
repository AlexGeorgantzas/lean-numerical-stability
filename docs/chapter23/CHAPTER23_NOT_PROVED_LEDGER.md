# Chapter 23 Not-Proved Ledger

The selected-scope gate is **PASS**. No selected Chapter 23 source row remains
open.

The formerly open rows are now discharged by actual rounded computations:

| Source row | Closing public endpoint | Status |
|---|---|---|
| (23.11), Miller | `higham23_eq23_11_miller_normwise` and `higham23_miller_normwiseRemainder_isBigO_u_sq` | PROVED |
| Theorem 23.3; (23.18) | `higham23_theorem23_3_winograd_closedCoefficient_firstOrder` and `higham23_winogradMajorantRemainder_isBigO_u_sq` | PROVED |
| Theorem 23.4; (23.19) | `higham23_theorem23_4_biniLotti_eq23_19` and `higham23_biniMajorantRemainder_isBigO_u_sq` | PROVED |
| 23.B3 / Problem 23.6 | `higham23_threeMStrassen_sourceCoefficient` and `higham23_threeMStrassenRemainders_isBigO_u_sq` | PROVED |

Empirical experiments, literature review, and optional benchmark problems
remain skipped under the chapter skill; they are not selected-scope proof
obligations.

Problems 23.8--23.9 are no longer in that optional queue: their exact block
inverse, upper-triangular specialization, recurrence, and exponent results are
proved in `NumStability.Source.Higham.Chapter23.Problem08`.

The removed synthetic first-order expansion and zero-error witness surfaces
remain excluded. Every stability endpoint above is derived from a literal
rounded evaluator.
