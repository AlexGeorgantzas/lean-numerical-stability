# Chapter 23 Not-Proved Ledger

There are no nonterminal selected rows. The selected-scope gate is **PASS**.

Actual rounded evaluators prove Theorem 23.1, conventional multiplication, all componentwise complex bounds, and the induced-infinity norm bounds (23.23)--(23.24). The generic Miller row, recursive Theorems 23.2--23.4, and 23.B3/Problem 23.6 are closed as **PASS (EXPLICIT-DOMAIN)** because the chapter either cites an external result without its constants/proof or omits the combined proof. Their shared `Higham23FirstOrderExpansion` premise records a local linear term and bounded quadratic coefficient, not the target norm inequality; `higham23_firstOrderExpansion_producer`, `higham23_firstOrderExpansion_nonempty`, and the named domain-producer theorems establish constructibility and nonvacuity.

Standard first-order `O(u²)` is represented by an explicit bounded coefficient multiplying `u²`. For the gamma-based actual evaluators, `higham23_gammaRemainder_isBigO_u_sq` additionally proves the Mathlib asymptotic statement at `u -> 0` with dimensions fixed.
