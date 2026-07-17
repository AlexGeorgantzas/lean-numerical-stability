# Higham Chapter 25 Formalization Report

## Outcome

Chapter 25 was audited end to end in core mode, including both Problems rows
and Appendix A solution 25.1. Exact Newton-step models, error-budget premises,
the normalized eigenproblem, first-order conditioning algebra, the structured
two-variable example, the stopping estimate, and all mathematical parts of
Problem 25.1 are formalized.

The chapter gate is **FAIL** because equation (25.11) is a selected precise
row and its implicit-function premise has not been produced from the source's
smoothness and nonsingularity assumptions. The literal feasible
limit-supremum condition number is formalized, and the new
`higham25_eq25_11_of_actualSolutionMap_hasFDerivAt` theorem derives the
Taylor-to-limit step from an ordinary Fréchet derivative. It still consumes an
actual unique solution-map contract; no local theorem yet constructs that map
from `F_x` nonsingular or proves that its derivative is `-F_x⁻¹ F_d`.
Equation (25.13) is closed by a literal rounded evaluator and an end-to-end producer of the
three existential error witnesses. Theorems 25.1 and 25.2 are intentionally not
declared with invented conclusions: `≈` and “decreases until” are undefined in
the source, and both proofs are citation-only.  They are stable
`DEFER-MISSING-PRECISE-STATEMENT` rows and do not themselves fail the gate.
Rheinboldt's under-specified max/min quotient and the cited local
residual/error constants are likewise deferred rather than converted into
invented propositions.

## Lean deliverables

- `LeanFpAnalysis/FP/Algorithms/Nonlinear/Higham25.lean`
  - exact and rounded Newton-step models for (25.1)-(25.2)
  - exact scalar predicates for (25.3)-(25.7)
  - `higham25EigenResidual` and the zero/eigenpair equivalence (25.10)
  - literal feasible sets/supremums, exact linearized sSup, actual unique
    solution-map and uniform Taylor contracts, and nonvacuity
  - `higham25_taylor_linear_bound_of_hasFDerivAt` and
    `higham25_eq25_11_of_actualSolutionMap_hasFDerivAt`, which replace the
    assumed Taylor contract by a genuine Fréchet-derivative argument while
    leaving the implicit-function producer visibly open
  - the three-error target predicate, literal rounded evaluator, end-to-end
    `u,u,gamma₃` producer, solution, and sensitivity facts for (25.12)-(25.13)
  - denominator and step-squared stopping bounds supporting (25.14)
- `LeanFpAnalysis/FP/Algorithms/Nonlinear/Higham25Problem25_1.lean`
  - Appendix equation (A.15)
  - fixed-point consequence of (25.15)
  - invariant ball and strict descent outside the ball
  - geometric envelope, boundedness, and the subsequential-limit bound

## Source-index repairs

- `chapter_splitting/chapter_index.md`: Chapter 25 now records six sections,
  includes §25.2, places Theorems 25.1-25.2 in that section, and lists both
  Problems 25.1 and 25.2.
- `chapter_splitting/split_primary_contracts.md`: Chapter 25 now records six
  sections, locates both named theorems in §25.2, and records two Problems.

Evidence: printed p. 461 / Chapter PDF 3 is headed “25.2 Error Analysis”; the
rendered Problems page, printed p. 469 / Chapter PDF 11, contains Problems 25.1
and 25.2; Appendix solution 25.1 spans printed pp. 569-570 / Appendix PDFs 43-44.

## Verification

- Focused Lean checks passed for both Chapter 25 modules at the audited
  baseline. After the gate correction, direct compilation of
  `Higham25.lean` passed with the new Fréchet-derivative limit theorem, and the
  focused module-target build passed (`2039` jobs).
- Forbidden-token scan found no `sorry`, `admit`, `axiom`, `unsafe`, or
  `opaque` declarations.
- `git diff --check` passed for the Chapter 25 files.
- `#print axioms` for
  `higham25_eq25_11_of_actualSolutionMap_hasFDerivAt` reports only `propext`,
  `Classical.choice`, and `Quot.sound`; the earlier audits of the old
  solution-map/Taylor endpoint and (25.13) producer reported the same list.

## Open selected row

Equation (25.11), printed p. 466 / PDF 8, remains open at the source-facing
implicit-function step. The exact dependency chain and next theorem are in
`docs/chapter25/CHAPTER25_BOTTLENECK_LEDGER.md`.

## Deferred source rows

1. Obtain a source-authoritative exact definition for the approximation and
   stopping claims in (25.8)-(25.9), then reconstruct Tisseur's proofs.
2. State Rheinboldt's quotient only after supplying nonempty compact domains,
   distinct-point/nonzero-denominator conditions, and extremum semantics.
3. Reconstruct the cited residual/error comparison only after choosing exact
   Taylor-remainder hypotheses and a neighborhood radius.
