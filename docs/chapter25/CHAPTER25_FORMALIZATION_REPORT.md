# Higham Chapter 25 Formalization Report

## Outcome

Chapter 25 was audited end to end in core mode, including both Problems rows
and Appendix A solution 25.1. Exact Newton-step models, error-budget premises,
the normalized eigenproblem, first-order conditioning algebra, the structured
two-variable example, the stopping estimate, and all mathematical parts of
Problem 25.1 are formalized.

The chapter gate is **PASS / SOURCE-DISCREPANCY** under the strict
precise-prose audit. Equation
(25.11) is derived directly from the
source's smoothness and nonsingularity assumptions. The source-facing theorem
instantiates Mathlib's implicit-function theorem, produces local data and
solution neighborhoods with existence and uniqueness, proves that the
solution-map derivative is `-F_x⁻¹ F_d`, and evaluates the literal
epsilon-indexed feasible `sSup`.
Equation (25.13) is closed by a literal rounded evaluator and an end-to-end producer of the
three existential error witnesses. Theorems 25.1 and 25.2 are intentionally not
declared with invented conclusions: `≈` and “decreases until” are undefined in
the source, and both proofs are citation-only.  They are stable
`DEFER-MISSING-PRECISE-STATEMENT` rows and do not themselves fail the gate.
Rheinboldt's under-specified max/min quotient and the cited local
residual/error constants are likewise deferred rather than converted into
invented propositions.

The p. 462-463 linear-system specialization is now closed by exact
Newton/refinement, constant-Jacobian, actual-residual, derivative-product, and
condition-number theorems. The source sentence `F=b-Ax, J=A` has a sign typo;
the implementation uses the correct derivative `J=-A`. The precise p. 463
eigenproblem prose has an actual bordered Jacobian, an exact Taylor identity,
kernel triviality directly from characteristic-polynomial root multiplicity
one, a nonzero determinant theorem for the displayed bordered matrix, and a
rounded `ψ` producer.
The printed eigen-Jacobian Lipschitz coefficient `2‖A‖` is false at `A=0`;
the formal development records the counterexample and proves the corrected
universal infinity-norm coefficient `2`.

## Lean deliverables

- `NumStability/Algorithms/Nonlinear/Higham25.lean`
  - exact and rounded Newton-step models for (25.1)-(25.2)
  - `higham25_linearSystem_newtonCorrection_iff_refinementCorrection`,
    `higham25_linearSystemJacobian_constant`,
    `higham25_linearSystemJacobian_lipschitz_zero`, and
    `higham25_linearSystem_actualResidual_bridge_ch12` for the linear-system
    special case
  - `higham25_linearSystemDataDerivativeFrob_eq` and
    `higham25_linearSystem_condition_frobenius` for the exact condition identity
  - exact scalar predicates for (25.3)-(25.7)
  - `higham25EigenResidual` and the zero/eigenpair equivalence (25.10)
  - literal feasible sets/supremums, exact linearized sSup, local and global
    solution-map contracts, and nonvacuity
  - `higham25_isContDiffImplicitAt_of_partialEquiv`,
    `higham25_implicitFunction_local_solution_contract`, and
    `higham25_implicitFunction_hasFDerivAt`, which produce the source's local
    unique solution map and derivative from the printed IFT hypotheses
  - `higham25_actualConditionValues_eq_localSolutionGraph` and
    `higham25_eq25_11_of_implicitFunction`, which close the literal (25.11)
    limit-supremum equality without a target-bearing assumption
  - the three-error target predicate, literal rounded evaluator, end-to-end
    `u,u,gamma₃` producer, solution, and sensitivity facts for (25.12)-(25.13)
  - denominator and step-squared stopping bounds supporting (25.14)
- `NumStability/Algorithms/Nonlinear/Higham25Problem25_1.lean`
  - Appendix equation (A.15)
  - fixed-point consequence of (25.15)
  - invariant ball and strict descent outside the ball
  - geometric envelope, boundedness, and the subsequential-limit bound
- `NumStability/Algorithms/Nonlinear/Higham25EigenClosure.lean`
  - displayed bordered Jacobian and exact derivative/Taylor bridge
  - algebraic simple-eigenpair certificate and its kernel-triviality theorem
  - direct generalized-eigenspace bridge from root multiplicity one to kernel
    triviality and nonzero determinant of the displayed bordered matrix
  - literal `n+1`-term rounded residual evaluator and printed `ψ` budget
  - corrected Lipschitz coefficient `2` and formal counterexample to `2‖A‖`

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

- Direct compilation of `Higham25.lean` passed. The fresh focused
  `Higham25EigenClosure` build passed (`3001/3001` jobs) with the direct
  algebraic-simple-eigenvalue producer. Repository-level verification is
  recorded in the Split 4 report.
- Forbidden-token scan found no `sorry`, `admit`, `axiom`, `unsafe`, or
  `opaque` declarations.
- `git diff --check` passed for the Chapter 25 files.
- `#print axioms` for both new algebraic-simple-eigenvalue endpoints reports
  only `propext`, `Classical.choice`, and `Quot.sound`; the same audit for
  `higham25_eq25_11_of_implicitFunction` has the identical standard basis.

## Open selected rows

None. The p. 463 simple-eigenvalue sentence is closed directly from algebraic
multiplicity one, without constructing `Higham25SimpleEigenpairCertificate`.
The false eigen-Jacobian coefficient is a separate recorded terminal source
discrepancy.

## Deferred source rows

1. Obtain a source-authoritative exact definition for the approximation and
   stopping claims in (25.8)-(25.9), then reconstruct Tisseur's proofs.
2. State Rheinboldt's quotient only after supplying nonempty compact domains,
   distinct-point/nonzero-denominator conditions, and extremum semantics.
3. Reconstruct the cited residual/error comparison only after choosing exact
   Taylor-remainder hypotheses and a neighborhood radius.
