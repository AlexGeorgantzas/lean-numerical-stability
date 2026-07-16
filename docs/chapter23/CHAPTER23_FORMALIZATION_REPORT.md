# Higham Chapter 23 Formalization Report

## Source and scope

- Edition: 2nd ed., SIAM, 2002.
- Chapter: 23, "Fast Matrix Multiplication", pp. 433--449.
- Mode: core; Split 4.
- Planning documents consulted: full blueprint, complete Split 4 contract, chapter index.
- Selected-scope gate: **PASS**.

## Completed selected targets

| Source | Lean declaration | Theorem surface | Notes |
|---|---|---|---|
| (23.2) | `higham23_eq23_2_winograd_identity` | exact paired finite-sum identity | even dimension represented as `m` adjacent pairs |
| Theorem 23.1 / (23.12), balanced scaling | actual rounded Winograd evaluator, factor expansion, error and balancing theorems | `n gamma_(n/2+4)` bound and displayed balanced coefficient | no target-equivalent error certificate; derived from `FPModel` operations and dot-product backward error |
| (23.10), (23.17) | actual conventional rounded matrix product, componentwise and max-entry envelope theorems | printed `nu` and `n²u` terms plus explicit quadratic remainder | remainder is formally `O(u²)` |
| (23.3)--(23.4) | `Higham23Block2`, `higham23BlockMul`, `higham23Strassen2`, correctness theorem | exact Strassen seven-product algorithm | valid for noncommutative blocks |
| (23.5) | `higham23StrassenCosts`, closed-form recurrence theorems | exact multiplication/addition counts | derived from executable recursive cost semantics |
| (23.6) | `higham23WinogradStrassen2`, correctness theorem | exact 15-addition variant | valid for noncommutative blocks |
| (23.7a)--(23.7b) | `Higham23BilinearAlgorithm`, product/evaluator definitions, source equations, correctness surface | exact coefficient tensors and one-level evaluator | recursive rounded evaluator remains part of Theorem 23.4 |
| (23.8)--(23.9) | `higham23ThreeM`, `higham23_eq23_9_threeM_correct` | exact three-product real/imaginary formula | valid for matrix blocks |
| (23.20)--(23.22), scaling prose | actual conventional and 3M rounded entry evaluators, exact-gamma/first-order theorems, gamma remainder `O(u²)`, diagonal budget invariance | componentwise real/imaginary bounds with printed leading coefficients | computed operations, not an error certificate |
| (23.16) | canonical Strassen coefficient, recurrence equation, and closed upper-coefficient theorem | exact recurrence arithmetic and displayed coefficient | no supplied recurrence certificate required |
| recurrence and coefficient in (23.18) | canonical Winograd--Strassen coefficient, step, and closed upper bound | exact recurrence arithmetic | computed recursive block path remains separate |
| (23.23)--(23.24) | actual conventional/3M imaginary-part matrices and induced complex infinity norm | exact-gamma normwise bounds with constants 2 and 4 | the 3M proof formalizes the printed `sqrt 2` weakening |
| (23.11) | `Higham23FirstOrderExpansion`, producer, witness, Miller theorem | generic first-order plus bounded quadratic remainder | PASS (EXPLICIT-DOMAIN), because the source states the result without proof or `f_n` |
| Theorems 23.2--23.3 / (23.14)--(23.18) | canonical recurrences, closed coefficients, named domain theorems, and producers | printed coefficients plus bounded quadratic remainder | PASS (EXPLICIT-DOMAIN) for the recursively rounded local expansion |
| Theorem 23.4 / (23.19) | tensor support count, positive `alpha`/`beta`, Bini--Lotti coefficient, domain theorem and producer | `n = h^depth` coefficient form | PASS (EXPLICIT-DOMAIN); exact external constants are not printed in the chapter |
| 23.B3 / Problem 23.6 | `higham23ThreeMStrassenCoefficient`, named theorem and producer | multiplier 6 and added 4 from the source prose | PASS (EXPLICIT-DOMAIN) |

## Reused results

- Conventional matrix multiplication and its exact/componentwise infrastructure are reused from repository matrix-multiplication modules.
- `StrassenRecurrence` and `WinogradStrassenRecurrence` are reused from `FastMatMul.lean`; the new module corrects source traceability to Chapter 23 without treating its certificate structures as proofs of the named error theorems.
- Lean's `noncomm_ring` tactic proves the exact block identities.

## Skipped material and explicit-domain scope

- No selected row remains open. Theorems 23.2--23.4, (23.11), and 23.B3/Problem 23.6 are explicitly domain-qualified because their complete rounded recursive operation graphs or external constants are not printed in the chapter. The local domain exposes linear and quadratic coefficients, has constructive producers and concrete witnesses, and is not target-equivalent to the final bound.
- Standard `O(u²)` content is an explicit bounded quadratic term. Gamma-based actual paths additionally carry a Mathlib `IsBigO` proof at `u -> 0` with fixed dimensions.
- Figures, historical machine speedups, random-matrix output, MATLAB output, and implementation anecdotes are skipped as empirical/editorial.
- All ten Problems and owned Appendix A rows 23.1, 23.2, 23.3, 23.5, 23.7, and 23.9 are inventoried. Problem 23.6 is a selected proof dependency for the precise 23.B3 combined 3M--Strassen bound; the other optional exact results are benchmark candidates.

## Selected-scope closure

Every selected row is terminal. Actual algorithms and FP paths prove Theorem 23.1/(23.12), balanced scaling, (23.5), (23.7), (23.10), (23.17), and (23.20)--(23.24). Citation-dependent recursive/generic claims are marked **PASS (EXPLICIT-DOMAIN)** in the inventory and proof-source ledger, with named nonvacuity producers. The not-proved ledger is empty.

## Hidden-hypothesis and weak-component audit

- Exact Strassen/Winograd--Strassen/3M correctness assumes only a nonunital nonassociative ring, which is weaker than the source's real matrix-block setting and does not assume the conclusion.
- No exact identity is described as a floating-point error theorem.
- The existing certificate structures in `FastMatMul.lean` were not counted as closures because their bound fields assume the advertised bound.
- `Higham23FirstOrderExpansion` is not such a certificate: it records the stronger operation-local identity `computed = exact + u*linear + u²*remainder` and independent entrywise coefficient bounds; the target norm inequality is derived from that identity.
- Weak components were independently checked by rendered-source comparison, Lean theorem types, focused compilation, and repository search.

## Verification

- Focused compile: `lake env lean LeanFpAnalysis/FP/Algorithms/FastMatMul/Higham23.lean` -- PASS.
- Joint narrow build: `lake build LeanFpAnalysis.FP.Algorithms.Vandermonde.Higham22 LeanFpAnalysis.FP.Algorithms.FastMatMul.Higham23` -- PASS (3063 jobs).
- Aggregate import compile and `examples/LibraryLookup.lean` -- PASS.
- Hygiene scan found no `sorry`, `admit`, new `axiom`, `unsafe`, or `opaque` declarations.
- Representative `#print axioms` on Theorem 23.1, (23.24), Theorems 23.2/23.4, and Problem 23.6 endpoints reported only `propext`, `Classical.choice`, and `Quot.sound`.

## Documentation

- Inventory: `docs/chapter23/CHAPTER23_SOURCE_INVENTORY.md`
- Not-proved ledger: `docs/chapter23/CHAPTER23_NOT_PROVED_LEDGER.md`
- Proof sources: `docs/chapter23/CHAPTER23_PROOF_SOURCE_LEDGER.md`
