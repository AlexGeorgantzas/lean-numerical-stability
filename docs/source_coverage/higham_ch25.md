# Higham Chapter 25 Source Coverage

- Source: `References/1.9780898718027.ch25.pdf`, printed pp. 459-469.
- Appendix: `References/1.9780898718027.appa.pdf`, solution 25.1, printed pp. 569-570.
- Audit: complete eleven-page chapter inspection, rendered Problems page, and
  rendered two-page Appendix solution inspection on 2026-07-16.
- Core status: **FAIL** under the strict precise-prose audit. The exact selected
  (25.11) limit-supremum equality is proved from
  the printed implicit-function hypotheses: the local unique solution map and
  derivative `-F_x⁻¹ F_d` are produced, not assumed. The literal
  rounded-evaluation producer for (25.13) is also proved. The p. 462-463 linear-
  system specialization is now closed end to end, including the actual Chapter
  12 residual evaluator and the Frobenius condition identity. The precise
  eigenproblem specialization following (25.10) is now produced by
  `Higham25EigenClosure.lean`: it proves the bordered Jacobian/Taylor identity,
  kernel-triviality from a constructive left/right/eigenspace certificate, and
  a literal rounded residual evaluator with the printed `ψ` budget. The bridge
  from a standard algebraic-multiplicity-one (simple-root) hypothesis to that
  certificate is not yet produced. The source's coefficient `2‖A‖` is also false without a
  scaling hypothesis (`A=0` is a formal counterexample); the correct universal
  infinity-norm coefficient `2` is proved instead. See
  `docs/chapter25/CHAPTER25_SOURCE_INVENTORY.md`.

## Coverage map

- Equations (25.1)-(25.7), (25.10), (25.12), (25.14), exact Newton models,
  eigenproblem, conditioning algebra helpers, example, and stopping bounds:
  `LeanFpAnalysis/FP/Algorithms/Nonlinear/Higham25.lean`.
- Problem 25.1 and Appendix (A.15):
  `LeanFpAnalysis/FP/Algorithms/Nonlinear/Higham25Problem25_1.lean`.
- Theorems 25.1/(25.8) and 25.2/(25.9):
  DEFER-MISSING-PRECISE-STATEMENT; no invented interpretation of `≈` or
  “decreases until.”
- Equation (25.11)'s local existence/uniqueness, derivative identity, literal
  feasible supremum, and Taylor-to-limit equality are closed by
  `higham25_eq25_11_of_implicitFunction` and its IFT support lemmas. Equation
  (25.13)'s actual floating evaluation is proved end to end. Rheinboldt's max/min quotient and
  the cited `1/2,2` local comparison are DEFER-MISSING-PRECISE-STATEMENT.
- The linear-system special case is covered by
  `higham25_linearSystem_newtonCorrection_iff_refinementCorrection`,
  `higham25_linearSystemJacobian_constant`,
  `higham25_linearSystemJacobian_lipschitz_zero`,
  `higham25_linearSystem_actualResidual_bridge_ch12`,
  `higham25_linearSystemDataDerivativeFrob_eq`, and
  `higham25_linearSystem_condition_frobenius`. The source's `F=b-Ax, J=A`
  sentence has a sign typo; Lean uses the derivative `J=-A`, whose sign cancels
  in the Newton equation. The p. 463 eigen-specialization prose is otherwise
  closed, with its false Lipschitz coefficient recorded as a terminal source
  discrepancy; the simple-eigenvalue bridge keeps the strict gate at `FAIL`.
- Problem 25.2: accounted-for research problem, excluded.
- Source audit corrected the section count to six, placed Theorems 25.1-25.2 in
  §25.2, and corrected the problem count to two.

Evidence ledgers:

- `docs/chapter25/CHAPTER25_SOURCE_INVENTORY.md`
- `docs/chapter25/CHAPTER25_FORMALIZATION_REPORT.md`
- `docs/chapter25/CHAPTER25_NOT_PROVED_LEDGER.md`
- `docs/chapter25/CHAPTER25_PROOF_SOURCE_LEDGER.md`
