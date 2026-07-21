# Higham Chapter 14 Source Inventory

## Audit Basis

- Audit date: 2026-07-18 (fresh strict producer audit)
- Source: `References/1.9780898718027.ch14.pdf`
- Book: Nicholas J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002)
- Chapter: 14, "Matrix Inversion", printed pp. 259-285
- Appendix source: `References/1.9780898718027.appa.pdf`, Chapter 14 solutions
- Mode: core, with the useful precise Problems listed below intentionally selected
- Parallel ownership: Split 3A, Chapter 14 only
- Source inspection: all 27 chapter PDF pages, relevant Appendix pages, extracted text, and rendered formula checks
- This file replaces the prior startup/partial inventory. It is a fresh source-order audit.

## Counts

There are **79 source rows** after separating Section 14.5's precise Schulz
claims from its surrounding survey prose:

- 69 intentionally selected mathematical rows.
- 10 policy exclusions: five empirical/figure/table rows, two expository/literature rows, and three optional Problems.
- Final selected-scope result: 66 selected rows close at determinate source
  strength, one is `DEFER-MISSING-PRECISE-STATEMENT`, and two are
  `SOURCE-ERROR/CORRECTED`; strict gate `PASS`, with every row terminally
  classified.
- The ten excluded rows remain explicitly accounted for below.

## Inventory

| # | Source row | Location | Decision / reason | Audit status | Primary Lean evidence |
|---:|---|---|---|---|---|
| 1 | Solve by a formed inverse | p. 260 | FORMALIZE_CORE / CORE-PRECISE-PROSE | PASS | `MatrixInversion.lean`: `inversion_residual_bound` |
| 2 | Table 14.1 | p. 260 | SKIP / SKIP-EMPIRICAL | EXCLUDED | Historical backward-error output; machine and implementation details are incomplete. |
| 3 | Figure 14.1 | pp. 261-262 | SKIP / SKIP-EMPIRICAL | EXCLUDED | MATLAB plot; no unique formal execution is specified. |
| 4 | Product-error notation `Delta(A1,...,Ak)` | p. 262 | FORMALIZE_DEPENDENCY / DEP-REQUIRED | PASS | `Ch14ProductErrorNotation.lean`: heterogeneous rectangular trees, arbitrary parenthesization, `exists_productDelta_gamma_operationBudget` |
| 5 | Equation (14.1) | p. 261 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `MatrixInversion.lean`: `ideal_right_residual` |
| 6 | Equation (14.2) | p. 261 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `MatrixInversion.lean`: `ideal_left_residual` |
| 7 | Equation (14.3) | p. 261 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14AsymptoticFamilies.lean`: `ch14ext_eq14_3_vanishing_family_endpoint` |
| 8 | Methods 1 and 2 | pp. 263-264 | FORMALIZE_DEPENDENCY / DEP-REQUIRED | PASS | `MatrixInversion.lean`, `Ch14Method2Loop.lean` |
| 9 | Equation (14.4) | p. 263 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `MatrixInversion.lean`: Method 1 right-residual theorem |
| 10 | Equation (14.5) | p. 263 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `MatrixInversion.lean`: Method 1 forward-error theorem |
| 11 | Equation (14.6) | p. 263 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14AsymptoticFamilies.lean`: `ch14ext_eq14_6_vanishing_family_endpoint` |
| 12 | Equation (14.7) | p. 263 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14AsymptoticFamilies.lean`: `ch14ext_eq14_7_vanishing_family_endpoint` |
| 13 | Lemma 14.1 | p. 264 | FORMALIZE_CORE / CORE-NAMED-RESULT | PASS | `Ch14Method2Loop.lean`: concrete reverse-column Method 2 residual closure |
| 14 | Equation (14.8) | p. 264 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14Method2Loop.lean` |
| 15 | Equation (14.9) | p. 265 | FORMALIZE_DEPENDENCY / DEP-REQUIRED | PASS | `Ch14BlockTriInverse.lean`: recursive block partition model |
| 16 | Lemma 14.2 | p. 265 | FORMALIZE_CORE / CORE-NAMED-RESULT | PASS | `Ch14Method1BWhole.lean` |
| 17 | Equation (14.10) | p. 265 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14Method1BWhole.lean` |
| 18 | Equation (14.11) | p. 265 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14Method1BWhole.lean` |
| 19 | Equation (14.12) | p. 265 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14Method1BWhole.lean` |
| 20 | Equation (14.13) | p. 266 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14Method1BWhole.lean` |
| 21 | Equation (14.14), Method 2B instability | p. 266 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `MatrixInversionMethod2BInstance.lean`, `Ch14Problem142Method2B.lean`; uncontrolled amplification retained |
| 22 | Lemma 14.3 | p. 267 | FORMALIZE_CORE / CORE-NAMED-RESULT | PASS | `Ch14Method2CWhole.lean` |
| 23 | Table 14.2 | p. 267 | SKIP / SKIP-EMPIRICAL | EXCLUDED | Cray 2 timing/rate data. |
| 24 | Method A | pp. 267-268 | FORMALIZE_DEPENDENCY / DEP-REQUIRED | PASS | `MatrixInversion.lean`: computed-column inverse path |
| 25 | Equation (14.15) | p. 268 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `MatrixInversion.lean`: Method A column backward error |
| 26 | Equation (14.16) | p. 268 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `MatrixInversion.lean`: Method A right residual |
| 27 | Equation (14.17) | p. 268 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `MatrixInversion.lean`: Method A forward error |
| 28 | Method B | p. 268 | FORMALIZE_DEPENDENCY / DEP-REQUIRED | PASS | `Ch14MethodsBC.lean`: concrete Doolittle and triangular-loop route |
| 29 | Equation (14.18) | p. 268 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14MethodsBC.lean`: `ch14ext_methodB_eq14_18_doolittle` |
| 30 | Method C | p. 269 | FORMALIZE_DEPENDENCY / DEP-REQUIRED | PASS | `Ch14MethodsBC.lean`: recursive stage construction |
| 31 | Equation (14.19) | p. 269 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14MethodsBC.lean`: `ch14ext_methodC_eq14_19_nat_doolittle` |
| 32 | Method D | p. 270 | FORMALIZE_DEPENDENCY / DEP-REQUIRED | PASS | `Ch14MethodDProductDischarge.lean` |
| 33 | Equation (14.20) | p. 270 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14MethodDLeftResidual.lean` |
| 34 | Equation (14.21) | p. 270 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14MethodDLeftResidual.lean` |
| 35 | Equation (14.22) | p. 270 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14MethodDLeftResidual.lean` |
| 36 | Equation (14.23) | p. 270 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14MethodDProductDischarge.lean`: `ch14ext_methodD_left_residual_doolittle` |
| 37 | Equation (14.23), normwise companion | p. 270 | FORMALIZE_DEPENDENCY / DEP-REQUIRED | PASS | `Ch14MethodDProductDischarge.lean`: infinity-norm endpoint |
| 38 | Equation (14.24) | p. 270 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `MatrixInversion.lean`: left/right residual comparison |
| 39 | Tables 14.3-14.5 | p. 272 | SKIP / SKIP-EMPIRICAL | EXCLUDED | Historical timings and performance rates. |
| 40 | Algorithm 14.4 | p. 273 | FORMALIZE_CORE / CORE-NAMED-RESULT | PASS | `GaussJordanPivoting.lean`, `Ch14GaussJordanSourceClosure.lean`: solution preservation and final solve |
| 41 | Equation (14.25a) | p. 274 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14GaussJordanSourceClosure.lean`: source-active matrix recurrence |
| 42 | Equation (14.25b) | p. 274 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14GaussJordanSourceClosure.lean`: local `gamma_3` matrix error |
| 43 | Equation (14.26) | p. 274 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14GaussJordanSourceClosure.lean`: local RHS recurrence and error |
| 44 | Equation (14.27) | p. 274 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | The structural-finalization producer writes eliminated dead-storage entries as zero, produces the actual final diagonal, and proves the literal accumulated matrix identity (with `I` for the source-normalized unit-diagonal case). |
| 45 | Equation (14.28) | p. 274 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14GaussJordanSourceClosure.lean`: literal unpropagated RHS sum |
| 46 | Equation (14.29) | p. 275 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `ch14ext_gjeFinalizedSourceTrace_stage2_forward_error_14_29_with_final_division` proves the source forward-error identity for the literal final-division output. |
| 47 | Equations (14.30a-c) | p. 275 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `ch14ext_gjeFinalizedSourceTrace_stage2_backward_error_14_30abc_with_final_division` proves the componentwise backward-error identities for the literal final-division output. |
| 48 | Fixed-matrix addendum to (14.30) | p. 275 | DEFER / DEFER-MISSING-PRECISE-STATEMENT | DEFER-MISSING-PRECISE-STATEMENT | The qualitative statement that a general final diagonal scaling has a "negligible effect" supplies neither a rounded scaling operation nor a quantitative transfer bound; inventing one would strengthen the source. |
| 49 | Table 14.6 | p. 276 | SKIP / SKIP-EMPIRICAL | EXCLUDED | GJE backward-error output for the example family; machine path is incomplete. |
| 50 | Theorem 14.5 | p. 276 | FORMALIZE_CORE / CORE-NAMED-RESULT | PASS (DETERMINATE CONTENT) | `Ch14GJEFinalDivisionClosure.lean` proves the exact actual-output residual and forward envelopes and literal first-order constants. Its explicit vanishing-roundoff realization proves the named remainders are `O(u^2)`; the PDF's unparameterized `O(u^2)` prose remains a terminal, non-gating deferral. |
| 51 | Equation (14.31) | p. 276 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | The exact residual envelope and its actual final-division remainder are proved from the structurally finalized trace. |
| 52 | Equation (14.32) | p. 276 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | The exact forward envelope is proved for the literal final-division output, with the required boundedness obtained in the displayed family realization rather than from an unproduced executor family. |
| 53 | Equation (14.33) | p. 276 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14GaussJordanQConstruction.lean`: exact residual decomposition, used by the source-active Theorem 14.5 closure |
| 54 | Corollary 14.6 | p. 277 | FORMALIZE_CORE / CORE-NAMED-RESULT | PASS (DETERMINATE CONTENT) | `ch14ext_cor146Finalized_vanishing_family_endpoint` proves the printed `8 n^3` residual and `8 n^(5/2)` relative-forward coefficients for the literal final-division output. `Ch14Cor146UniformInverseBridge.lean` constructs the scaled inverse and regularity from the visible SPD policy; the source's unparameterized `O(u^2)` prose is terminally deferred. |
| 55 | Corollary 14.7 | p. 277 | FORMALIZE_CORE / CORE-NAMED-RESULT | PASS (DETERMINATE CONTENT) | `ch14ext_cor147Finalized_vanishing_family_endpoint` proves the printed `32 n^2` residual and `4 n^3 (kappa_inf(A)+3)` forward coefficients for the literal final-division output, while `Ch14Cor147SourceDomainConstructor.lean` constructs the row-dominant domain witnesses; the source's unparameterized `O(u^2)` prose is terminally deferred. |
| 56a | Schulz inverse iteration | p. 278 | FORMALIZE_CORE / CORE-PRECISE-PROSE | PASS | `Ch14SchulzIteration.lean`: both exact update forms, left/right residual squaring, `E_k = E_0^(2^k)`, quadratic/double-exponential norm bounds, residual and inverse convergence, and the printed `X_0 = alpha A^T`, `0 < alpha < 2/||A||_2^2` criterion. |
| 56b | Remaining parallel inversion discussion | p. 278 | DEFER / DEFER-MISSING-PRECISE-STATEMENT | EXCLUDED | Csanky's method, processor/complexity comparisons, acceleration suggestions, and qualitative floating-point stability observations; future benchmark material. |
| 57 | Hadamard condition number `psi(A)` | p. 279 | FORMALIZE_CORE / CORE-PRECISE-PROSE | SOURCE-ERROR/CORRECTED | Printed `det(D)/det(A)` can be negative. `MatrixInversion.lean` uses `abs(det A)`; `Ch14SourceCorrections.lean` proves the `[-1]` witness. |
| 58 | Equation (14.34) | p. 279 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `MatrixInversion.lean`: signed and absolute GEPP determinant products |
| 59 | Hyman determinant method | p. 280 | FORMALIZE_DEPENDENCY / DEP-REQUIRED | PASS | `Ch14HymanDeterminant.lean` |
| 60 | Equation (14.35) | p. 280 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14HymanDeterminant.lean` |
| 61 | Equation (14.36) | p. 280 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14HymanDeterminant.lean` |
| 62 | Section 14.7 notes | pp. 281-282 | SKIP / SKIP-LITERATURE-REVIEW | EXCLUDED | Bibliographic and historical notes. |
| 63 | Problem 14.1 | p. 283 | SKIP / OPTIONAL-PROBLEM-NOT-SELECTED | EXCLUDED | Reflective historical anecdote, not a precise theorem. |
| 64 | Problem 14.2 | p. 283; App. A p. 558 | FORMALIZE_CORE / CORE-PRECISE-PROSE | PASS | `Ch14Problem142Families.lean`: uniform (13.4)/(13.5) family analysis for Methods 1B, 2C, and Method 2B obstruction |
| 65 | Problem 14.3 | p. 283; App. A p. 558 | FORMALIZE_CORE / CORE-PRECISE-PROSE | PASS | `MatrixInversion.lean`: condition-number residual comparison |
| 66 | Problem 14.4 | p. 283; App. A p. 558 | FORMALIZE_CORE / CORE-SYMBOLIC-EXAMPLE | PASS | `MatrixInversion.lean`: parametrized 2-by-2 residual-ratio family |
| 67 | Problem 14.5 | p. 283; App. A p. 559 | FORMALIZE_CORE / CORE-PRECISE-PROSE | PASS | `Ch14AsymptoticFamilies.lean`: left/right vanishing-family endpoints |
| 68 | Problem 14.6 | p. 283; App. A p. 559 | SKIP / OPTIONAL-PROBLEM-NOT-SELECTED | EXCLUDED | Optional extension not selected in core mode. |
| 69 | Problem 14.7 | p. 284; App. A p. 559 | FORMALIZE_CORE / CORE-PRECISE-PROSE | PASS | `MatrixInversion.lean`: exact selected closure |
| 70 | Problem 14.8 | p. 284; App. A p. 559 | FORMALIZE_CORE / CORE-PRECISE-PROSE | PASS | `MatrixInversion.lean` |
| 71 | Problem 14.9 | p. 284 | SKIP / OPTIONAL-PROBLEM-NOT-SELECTED | EXCLUDED | Optional mixed forward-backward exercise not selected in core mode. |
| 72 | Problem 14.10 | p. 284; App. A p. 560 | FORMALIZE_CORE / CORE-PRECISE-PROSE | PASS | `MatrixInversion.lean` |
| 73 | Problem 14.11 | p. 284; App. A p. 560 | FORMALIZE_CORE / CORE-PRECISE-PROSE | PASS | `MatrixInversion.lean`: Hadamard inequality and equality characterization |
| 74 | Problem 14.12 | p. 284; App. A p. 560 | FORMALIZE_CORE / CORE-PRECISE-PROSE | PASS | `MatrixInversion.lean`: QR/row-scaling identities |
| 75 | Problem 14.13 | p. 284; App. A p. 560 | FORMALIZE_CORE / CORE-PRECISE-PROSE | PASS | `Ch14Problem1413Boundary.lean`: all positive dimensions, including `n=1` |
| 76 | Equation (14.37) | p. 284 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Ch14Problem1413Boundary.lean` |
| 77 | Problem 14.14 | p. 285; App. A p. 560 | FORMALIZE_CORE / CORE-PRECISE-PROSE | PASS | `Ch14HymanDeterminant.lean`: `gamma_(2n-1)` backward error and scaling invariance |
| 78 | Problem 14.15 | p. 285; App. A pp. 560-561 | FORMALIZE_CORE / CORE-PRECISE-PROSE | SOURCE-ERROR/CORRECTED | Printed guard `< 1` does not keep `1-nx` positive. `Chapter14Problem1415Weyl.lean` proves the corrected `< 1/n` theorem and a checked `n=2, x=3/4` counterexample. |

## Source Corrections

1. **Hadamard `psi`:** the printed signed denominator contradicts `psi(A) >= 1` for matrices with negative determinant. The formal condition number uses `|det(A)|`; the signed raw definition remains available and has a checked negative witness.
2. **Problem 14.15:** the printed hypothesis permits a negative right-hand denominator. The proved theorem uses the necessary card-dependent guard `kappa_2(A) ||Delta A||_2 / ||A||_2 < 1/n`.

## Exclusion Accounting

The ten excluded rows are source-visible and intentional. None is being counted as an unproved mathematical theorem. Tables 14.1, 14.2, 14.3-14.5, Table 14.6, and Figure 14.1 are empirical artifacts; the remaining parallel-method prose and notes rows are literature/exposition; Problems 14.1, 14.6, and 14.9 are optional and not selected.
