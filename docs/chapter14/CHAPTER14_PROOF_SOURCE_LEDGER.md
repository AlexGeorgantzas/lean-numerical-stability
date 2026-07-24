# Chapter 14 Proof-Source Ledger

## Scope

This ledger records every nontrivial proof source used during the 2026-07-15 from-scratch audit of Higham Chapter 14. A citation or model contract was not treated as a proof of a stronger Lean theorem.

| Source | Exact role | Lean disposition | Status |
|---|---|---|---|
| Higham, 2nd ed., Chapter 14, pp. 259-285 | Primary statements, algorithms, constants, and proof sketches | Compared row-by-row with the 78-row inventory and local Lean theorem types | ADOPTED AND FORMALIZED |
| Higham, Appendix A, Chapter 14 solutions, pp. 558-561 | Proof routes and missing details for selected Problems 14.2-14.5, 14.7-14.8, and 14.10-14.15 | Used as mathematical guidance; every adopted step is proved locally | ADOPTED AND FORMALIZED |
| Higham Chapters 3, 8, 9, and 13 | Source-cited matrix product, triangular solve, LU, condition, and BLAS assumptions | Reused existing repository declarations; no chapter-crossing axiom added | REUSED |
| Mathlib finite matrices, determinants, norms, topology, and asymptotics | Standard algebra, determinant continuity, l2 operator norm, singular values, and Landau calculus | Imported through normal modules; headline axiom audits show only `propext`, `Classical.choice`, and `Quot.sound` | REUSED |
| Existing `NumStability` matrix algebra and FP model | `fl_matMul`, triangular solves, LU certificates, exact matrix norms, inverse identities, and Chapter 9 bounds | Reused rather than duplicated; new Chapter 14 wrappers instantiate these paths | REUSED |
| Rendered chapter and Appendix pages in `tmp/pdfs/` | Visual verification of formulas, labels, signs, denominators, and omitted empirical rows | Audit evidence only; never staged or pushed | ADVISORY |
| Oracle / GPT-5.5 Pro review attempt | Requested second-model review of difficult closure points | Session stalled without a substantive mathematical answer; no claim or proof was adopted | REJECTED / NO OUTPUT |

## Independent Audit Record

| Audited surface | Independent result | Disposition |
|---|---|---|
| Generic GJE printed-envelope helper | Found that the older unmasked family endpoint carried `Xabs = O(1)` as a premise | Kept only as an algebraic helper; not used as the final chapter closure |
| Source-active Algorithm 14.4 through Theorem 14.5 | Verified the masked trace, exact (14.30)-(14.32) factors/constants, derived `Pabs`/`Q`/`Xabs` boundedness, explicit remainders, and standard axioms | PASS |
| Corollary 14.6 initial candidate | Found that the printed constants were proved only through the older unmasked GJE recurrence | Rejected as the final row-54 evidence |
| Corollary 14.6 source-active repair | `Ch14Corollary146SourceClosure.lean` carries the SPD norm and asymptotic closure through the masked Algorithm 14.4 trace, with exact `8 n^3` and `8 n^(5/2)` constants and explicit `O(u^2)` remainders | PASS |
| Corollary 14.7 source and mathematics | Verified source normalization, exact `32 n^2` residual and `4 n^3 (kappa_inf(A)+3)` forward constants, factor/inverse proximity induction, ratio absorption, nonvacuity, and explicit `O(u^2)` remainders | PASS |
| Corollary 14.7 Lean/trust closure | Re-typechecked the final module, recursively audited assumptions/imports, and printed headline axioms | PASS; only `propext`, `Classical.choice`, and `Quot.sound` |

## Imported Claims Closed Locally

| Claim | Source route | Local closure |
|---|---|---|
| Arbitrary-order compatible matrix product error | Chapter 14 notation plus Chapter 3 matrix-product model | `Ch14ProductErrorNotation.lean`: rectangular typed trees and operation-budget `gamma_p` theorem |
| Method 2B instability under (13.4)/(13.5) | Chapter 14 and Appendix A, Problem 14.2 | `Ch14Problem142Method2B.lean`, `Ch14Problem142Families.lean` |
| All-index singular-value perturbation needed by Problem 14.15 | Weyl/Mirsky route used by the Appendix argument | `Chapter14Problem1415Weyl.lean`; no spectral inequality remains assumed at the final endpoint |
| Hadamard inequality equality case | Problem 14.11 / standard determinant theory | `MatrixInversion.lean`: inequality and orthogonal-row equivalence |
| Positive-dimension boundary in Problem 14.13 | Appendix AM-GM proof starts at dimension two | `Source/Higham/Chapter14/Problem13.lean` separately proves `n=1` and combines it with the general result |

## Source Errors

| Printed item | Evidence | Repair |
|---|---|---|
| `psi(A)=det(D)/det(A)` followed by `psi(A)>=1` | The one-by-one matrix `[-1]` gives raw value `-1` | Keep a raw signed definition, use `det(D)/|det(A)|` for the condition number, and prove the witness in `Source/Higham/Chapter14/Discrepancies.lean` |
| Problem 14.15 assumes only `x<1` while the bound divides by `1-nx` | At `n=2`, `x=3/4`, the displayed right side is negative | Prove the corrected card guard `x<1/n` and retain the checked scalar specialization in `Chapter14Problem1415Weyl.lean` |

## Trust Result

No external prose result was introduced as a Lean `axiom`, and no second-model output was used. Every selected closure is proved from repository/Mathlib declarations. The three final source-facing endpoints typecheck and their recursive axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
