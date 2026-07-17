# Chapter 14 Proof-Source Ledger

## Scope

This ledger records every nontrivial proof source used during the 2026-07-15
from-scratch audit and the 2026-07-17 completion re-audit of Higham Chapter 14.
A citation or model contract was not treated as a proof of a stronger Lean
theorem.

| Source | Exact role | Lean disposition | Status |
|---|---|---|---|
| Higham, 2nd ed., Chapter 14, pp. 259-285 | Primary statements, algorithms, constants, and proof sketches | Compared row-by-row with the corrected 82-row inventory and local Lean theorem types | SELECTED CORE SCOPE FORMALIZED |
| Higham, Appendix A, Chapter 14 solutions, pp. 558-561 | Proof routes and missing details for selected Problems 14.2-14.5, 14.7-14.8, and 14.10-14.15 | Used as mathematical guidance; every adopted step is proved locally | ADOPTED AND FORMALIZED |
| Higham Chapters 3, 8, 9, and 13 | Source-cited matrix product, triangular solve, LU, condition, and BLAS assumptions | Reused existing repository declarations; no chapter-crossing axiom added | REUSED |
| Mathlib finite matrices, determinants, norms, topology, and asymptotics | Standard algebra, determinant continuity, l2 operator norm, singular values, and Landau calculus | Imported through normal modules; headline axiom audits show only `propext`, `Classical.choice`, and `Quot.sound` | REUSED |
| Existing `LeanFpAnalysis` matrix algebra and FP model | `fl_matMul`, triangular solves, LU certificates, exact matrix norms, inverse identities, and Chapter 9 bounds | Reused rather than duplicated; new Chapter 14 wrappers instantiate these paths | REUSED |
| Rendered chapter and Appendix pages in `tmp/pdfs/` | Visual verification of formulas, labels, signs, denominators, and omitted empirical rows | Audit evidence only; never staged or pushed | ADVISORY |
| Oracle session `ch14-schulz-initialize`, GPT-5.5 Pro, 2026-07-17 | Math-only review of the p. 278 spectral initializer and rectangular nullspace issue; packet `scratch/chapter14/ch14_schulz_initializer_oracle_packet.md` | Partly adopted: the support/error route was translated and proved locally.  The final exact norm bound, right-Gram diagonalization, arbitrary-rank compact-SVD construction, and convergence proof were developed and checked locally.  Oracle's native transcript is `/u501/m2fetrat/.oracle/sessions/ch14-schulz-initialize/artifacts/transcript.md`; the separate stable-header harvest failure remains an operational record only. | PARTLY ADOPTED; ALL USED MATHEMATICS LOCALLY PROVED |

## Independent Audit Record

| Audited surface | Independent result | Disposition |
|---|---|---|
| Generic GJE printed-envelope helper | Found that the older unmasked family endpoint carried `Xabs = O(1)` as a premise | Kept only as an algebraic helper; not used as the final chapter closure |
| Source-active Algorithm 14.4 through Theorem 14.5 | Verified the masked trace, exact (14.30)-(14.32) factors/constants, derived `Pabs`/`Q`/`Xabs` boundedness, explicit remainders, and standard axioms | PASS |
| Corollary 14.6 initial candidate | Found that the printed constants were proved only through the older unmasked GJE recurrence | Rejected as the final row-54 evidence |
| Corollary 14.6 source-active repair | `Ch14Corollary146SourceClosure.lean` carries the SPD norm and asymptotic closure through the masked Algorithm 14.4 trace, with exact `8 n^3` and `8 n^(5/2)` constants and explicit `O(u^2)` remainders | PASS |
| Corollary 14.7 source and mathematics | Verified source normalization, exact `32 n^2` residual and `4 n^3 (kappa_inf(A)+3)` forward constants, factor/inverse proximity induction, ratio absorption, nonvacuity, and explicit `O(u^2)` remainders | PASS |
| Corollary 14.7 Lean/trust closure | Re-typechecked the final module, recursively audited assumptions/imports, and printed headline axioms | PASS; only `propext`, `Classical.choice`, and `Quot.sound` |
| p. 278 parallel-inversion aggregate exclusion | Rendered-page inspection found exact Schulz step, convergence, and residual-power claims inside the row previously classified wholly as literature | Prior exclusion rejected; precise claims split into inventory rows 56a--56c |
| p. 278 Schulz algebra | Checked the two printed step forms and left/right residual recurrence directly | `Ch14SchulzIteration.lean` proves the step equality and `E_k=E_0^(2^k)`; PASS |
| p. 278 Schulz initializer convergence | Compared the rendered source condition `0<alpha<2/‖A‖₂^2` and both inverse targets with the theorem types | PASS: `ch14ext_rectSchulzIter_tendsto_canonicalMoorePenrose_of_lt_two_div_norm_sq` proves arbitrary rectangular convergence to a locally certified Moore--Penrose inverse; `ch14ext_schulzIter_tendsto_inverse_of_lt_two_div_norm_sq` proves the square inverse clause |
| p. 278 Moore--Penrose support route | Pro review identified that the uncompressed right residual has eigenvalue `1` on `ker A`, and suggested proving `Aplus-X_k=(I-X_kA)Aplus` before spectral decay | Adopted after local proof: the support/error identities in `Ch14SchulzIteration.lean` are combined in `Ch14SchulzSpectralConvergence.lean` with an exact complexified rectangular operator norm, right-Gram eigenvalue bound and diagonalization, null-direction annihilation from the Penrose equations, and a canonical arbitrary-rank compact SVD |
| p. 278 initializer domain audit | Checked the quotient condition at `A=0` and across rank-deficient rectangular matrices | No full-rank hypothesis is needed.  The printed strict quotient condition is unsatisfiable at zero under Lean's total division; `ch14ext_rectSchulzIter_tendsto_canonicalMoorePenrose` proves the nonvacuous all-matrix internal form `0<alpha` and `alpha*(opNorm2 A)^2<2`. |
| Corollary 14.7 regularity fields | Inspected `Ch14Cor147SourceFamily` rather than relying on the report summary | `P_abs_isBigO_one` and `X_abs_isBigO_one` are explicit source-family fields; factor/inverse proximity is derived.  These are visible asymptotic regularity contracts, not target-shaped residual/forward assumptions. |

## Imported Claims Closed Locally

| Claim | Source route | Local closure |
|---|---|---|
| Arbitrary-order compatible matrix product error | Chapter 14 notation plus Chapter 3 matrix-product model | `Ch14ProductErrorNotation.lean`: rectangular typed trees and operation-budget `gamma_p` theorem |
| Method 2B instability under (13.4)/(13.5) | Chapter 14 and Appendix A, Problem 14.2 | `Ch14Problem142Method2B.lean`, `Ch14Problem142Families.lean` |
| All-index singular-value perturbation needed by Problem 14.15 | Weyl/Mirsky route used by the Appendix argument | `Chapter14Problem1415Weyl.lean`; no spectral inequality remains assumed at the final endpoint |
| Hadamard inequality equality case | Problem 14.11 / standard determinant theory | `MatrixInversion.lean`: inequality and orthogonal-row equivalence |
| Positive-dimension boundary in Problem 14.13 | Appendix AM-GM proof starts at dimension two | `Ch14Problem1413Boundary.lean` separately proves `n=1` and combines it with the general result |
| Arbitrary-rank Moore--Penrose existence for the Schulz target | Right-Gram spectral basis plus the compact-SVD Penrose theorem already proved for Chapter 20 Problem 20.3 | `Ch14SchulzSpectralConvergence.lean` selects exactly the nonzero right-Gram singular directions, proves the compact-SVD certificate including rank zero, and instantiates `higham20_problem20_3_compactSVD_moorePenrose` |

## Source Errors

| Printed item | Evidence | Repair |
|---|---|---|
| `psi(A)=det(D)/det(A)` followed by `psi(A)>=1` | The one-by-one matrix `[-1]` gives raw value `-1` | Keep a raw signed definition, use `det(D)/abs(det(A))` for the condition number, and prove the witness in `Ch14SourceCorrections.lean` |
| Problem 14.15 assumes only `x<1` while the bound divides by `1-nx` | At `n=2`, `x=3/4`, the displayed right side is negative | Prove the corrected card guard `x<1/n` and retain the checked scalar specialization in `Chapter14Problem1415Weyl.lean` |

## Trust Result

No external prose result was introduced as a Lean `axiom`.  The Pro review's
support-projection idea was used only after translation into locally checked
Lean declarations.  Every declaration offered as proved is derived from
repository/Mathlib declarations.  The named GJE and Schulz source-facing
endpoints typecheck, and their recursive axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`.  The selected core inventory has no open
proof-source row.
