# Higham Chapter 25 Source Coverage

- Source: `References/1.9780898718027.ch25.pdf`, printed pp. 459-469.
- Appendix: `References/1.9780898718027.appa.pdf`, solution 25.1, printed pp. 569-570.
- Audit: complete eleven-page chapter inspection, rendered Problems page, and
  rendered two-page Appendix solution inspection on 2026-07-16.
- Core status: **FAIL** at equation (25.11); under-specified
  named/citation-only rows are stably deferred. The exact selected (25.11)
  limit-supremum equality is proved only from a supplied local unique-solution
  map with a genuine derivative. The implicit-function producer of that map
  and its derivative identity remains open. The literal rounded-evaluation
  producer for (25.13) is proved. See
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
- Equation (25.11)'s literal feasible supremum and Taylor-to-limit equality are
  proved from `Higham25ActualSolutionMapContract` plus `HasFDerivAt`; that
  contract assumes the source's local existence/uniqueness conclusion, and no
  theorem yet constructs it from smooth `F` and nonsingular `F_x` or proves
  derivative `-F_x⁻¹ F_d`. Thus (25.11) remains selected and open. Equation
  (25.13)'s actual floating evaluation is proved end to end. Rheinboldt's max/min quotient and
  the cited `1/2,2` local comparison are DEFER-MISSING-PRECISE-STATEMENT.
- Problem 25.2: accounted-for research problem, excluded.
- Source audit corrected the section count to six, placed Theorems 25.1-25.2 in
  §25.2, and corrected the problem count to two.

Evidence ledgers:

- `docs/chapter25/CHAPTER25_SOURCE_INVENTORY.md`
- `docs/chapter25/CHAPTER25_FORMALIZATION_REPORT.md`
- `docs/chapter25/CHAPTER25_NOT_PROVED_LEDGER.md`
- `docs/chapter25/CHAPTER25_PROOF_SOURCE_LEDGER.md`
