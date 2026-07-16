# Higham Chapter 25 Source Coverage

- Source: `References/1.9780898718027.ch25.pdf`, printed pp. 459-469.
- Appendix: `References/1.9780898718027.appa.pdf`, solution 25.1, printed pp. 569-570.
- Audit: complete eleven-page chapter inspection, rendered Problems page, and
  rendered two-page Appendix solution inspection on 2026-07-16.
- Core status: **PASS**; under-specified named/citation-only rows are stably
  deferred. The exact selected (25.11) limit-supremum equality and literal
  rounded-evaluation producer for (25.13) are proved. See
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
- Equation (25.11)'s literal feasible supremum and limit equality are proved on
  an explicit unique-solution-map/Taylor domain, with a concrete nonvacuity
  witness. (25.13)'s actual floating evaluation is proved end to end. Rheinboldt's max/min quotient and
  the cited `1/2,2` local comparison are DEFER-MISSING-PRECISE-STATEMENT.
- Problem 25.2: accounted-for research problem, excluded.
- Source audit corrected the section count to six, placed Theorems 25.1-25.2 in
  §25.2, and corrected the problem count to two.

Evidence ledgers:

- `docs/chapter25/CHAPTER25_SOURCE_INVENTORY.md`
- `docs/chapter25/CHAPTER25_FORMALIZATION_REPORT.md`
- `docs/chapter25/CHAPTER25_NOT_PROVED_LEDGER.md`
- `docs/chapter25/CHAPTER25_PROOF_SOURCE_LEDGER.md`
