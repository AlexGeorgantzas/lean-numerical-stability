# Higham Chapter 23 Formalization Report

## Outcome

The selected-scope gate is **PASS**. All source-facing stability results are
proved from actual rounded evaluators, including the four rows that were
previously open.

The canonical complete entry point is
`NumStability.Source.Higham.Chapter23`. Its 26 declaration-bearing modules are
split by mathematical role, equation, named theorem, algorithm family, and
problem. Five declaration-free aggregates provide the complete chapter and
the Theorem 23.2, Theorem 23.3, Bini--Lotti, and combined 3M--Strassen family
surfaces. The six historical `NumStability.Algorithms.FastMatMul.Higham23*`
paths remain import-only compatibility wrappers; new code should not import
them.

## Proved source-facing work

| Source | Lean surface | Result |
|---|---|---|
| (23.2) | paired Winograd finite-sum identity | exact algebra proved |
| (23.3)--(23.4) | `Higham23Block2`, `higham23Strassen2` | exact seven-product correctness proved |
| (23.5) | executable Strassen cost recurrence | printed multiplication/addition counts proved |
| (23.6) | `higham23WinogradStrassen2` and `higham23FlWinogradStrassenRecursive` | exact 15-addition identity and literal rounded recursion proved |
| (23.7a)--(23.7b) | exact and rounded recursive bilinear evaluators | noncommutative correctness transfer and tensor-weight error induction proved |
| (23.8)--(23.9) | `higham23ThreeM` | exact three-real-product identity proved |
| (23.10), (23.17) | actual rounded conventional multiplication | componentwise/max-entry bounds with quadratic remainder proved |
| (23.11) | `higham23MillerFlEvaluate` | literal coefficient dots, bilinear products, and output reconstruction; explicit `f_n` and `O(u²)` remainder proved |
| Theorem 23.1 / (23.12) | actual rounded Winograd inner product | printed error bound and balancing theorem proved |
| Theorem 23.2 / (23.14)--(23.16) | `higham23FlStrassenRecursive` | exact nonlinear induction, printed 12/46 closed coefficient, and `O(u²)` remainder proved |
| Theorem 23.3 / (23.18) | `higham23FlWinogradStrassenRecursive` | exact nonlinear induction, printed 18/89 closed coefficient, and `O(u²)` remainder proved |
| Theorem 23.4 / (23.19) | `higham23BiniFlEvaluate` | explicit algorithm-dependent `alpha`,`beta`, source envelope, and `O(u²)` remainder proved |
| (23.20)--(23.24) | actual rounded conventional and 3M complex paths | componentwise, scaling, and induced-infinity bounds proved |
| 23.B3 / Problem 23.6 | `higham23FlThreeMStrassen` | rounded input sums, three recursive Strassen products, rounded outputs, source `6*(c+4)` coefficient, and `O(u²)` remainders proved |
| Problems 23.8--23.9 | `higham23Problem23_8Candidate`, `higham23_problem23_8_block_inverse` | noncommutative block inverse, upper-triangular specialization, exact cost recurrence, and power-law exponent proved |

## Source correction

For `n = h^depth`, equation (23.19)'s factor
`n^(log_h beta) log_h n` is `beta^depth * depth`. The stale scalar placeholder
had an extra `h^depth`; `higham23BiniLottiCoefficient` now records the correct
algebraic form.

## Verification

- `lake build NumStability.Source.Higham.Chapter23` is the canonical complete
  chapter gate.
- Independent builds cover all 26 canonical declaration leaves and all five
  canonical aggregates.
- Six old-only import tests cover the historical
  `NumStability.Algorithms.FastMatMul.Higham23*` compatibility surfaces without
  co-importing the canonical chapter aggregate.
- `lake build NumStability.Algorithms` and
  `lake env lean examples/LibraryLookup.lean` remain integration gates.
- Axiom audits for the Miller, Winograd--Strassen, Bini--Lotti, and combined
  3M--Strassen endpoints report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- The canonical modules contain no `sorry`, `admit`, `axiom`, `unsafe`, or
  `opaque` declaration.

See the inventory and proof-source ledger for row-level routes.
