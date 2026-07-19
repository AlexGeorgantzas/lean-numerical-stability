# Higham Chapter 25 Source Inventory

## Audit basis

- Audit date: 2026-07-16.
- Primary source: `References/1.9780898718027.ch25.pdf`, SHA-256 `E5534965F8A5AA8744021D446BA7F349D8DAEBC5C1D49B0090C51D2984E06A57`.
- Appendix source: `References/1.9780898718027.appa.pdf`, SHA-256 `8D4A7F7E99A95E19AD0F589342E287ECA469453F448535B718C1F805115101A2`.
- Book: Nicholas J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 25, “Nonlinear Systems and Newton's Method,” printed pp. 459-469, PDF pages 1-11.
- Appendix inspection: solution 25.1, printed pp. 569-570 / Appendix PDF pages 43-44, including (A.15).
- Inspection: all eleven chapter pages, both rendered Problems rows, Figure 25.1, and both Appendix solution pages were text-extracted and visually checked.
- Mode: core. Named results, printed equations, exact algorithms, precise quantitative prose, symbolic examples, and Problem 25.1 (because it supplies a reusable selected contraction theorem) are selected.

## Planning corrections found by the source audit

- Chapter 25 has **six** numbered sections. The former index omitted §25.2, “Error Analysis,” printed p. 461 / PDF 3.
- Theorems 25.1 and 25.2 occur in §25.2, not §25.1 as the former planning ledger stated.
- The Problems page has **two** rows, Problems 25.1 and 25.2, printed p. 469 / PDF 11. The former count of one problem was incorrect.
- Appendix A provides a solution for Problem 25.1 on printed pp. 569-570.

The selected-scope gate is **FAIL** under the strict precise-prose audit.
Equation (25.11) is derived from the
hypotheses printed on pp. 464-466. The new source-facing chain instantiates
Mathlib's implicit-function theorem from smoothness of `F` and an invertible
solution partial `F_x`, produces genuine local data and solution
neighborhoods, proves local existence and uniqueness, identifies the solution
map derivative as `-F_x⁻¹ F_d`, and evaluates the literal shrinking-ball
`sSup`. Equation (25.13), including production of its three witnesses from a
literal rounded evaluation order, is also proved. Theorems
25.1 and 25.2 cannot be stated at source strength without
defining the printed `≈` relation and “decreases until” event, so the skill's
`DEFER-MISSING-PRECISE-STATEMENT` rule applies. The precise p. 463 eigenproblem
specialization after (25.10) is substantially produced in
`Higham25EigenClosure.lean`: the bordered matrix and exact Taylor identity,
kernel triviality from an explicit left/right/eigenspace certificate, and the
literal rounded residual `ψ` bound are proved. The remaining strict gap is a
producer from the source's standard simple-eigenvalue hypothesis (algebraic
multiplicity one) to that certificate. The printed Lipschitz coefficient
`2‖A‖` is independently false for `A=0`; Lean proves that counterexample and
the corrected universal infinity-norm coefficient `2`.

## Named results

| Source row | Location | Decision | Evidence and status |
|---|---|---|---|
| Theorem 25.1 (Tisseur), limiting accuracy (25.8) | pp. 461-462 / PDFs 3-4 | DEFER-MISSING-PRECISE-STATEMENT | Exact premises (25.3)-(25.7) have local definitions. The conclusion uses undefined `≈` and “decreases until”; proof is only “See Tisseur §2.2.” **DEFERRED**. |
| Theorem 25.2 (Tisseur), limiting residual (25.9) | p. 462 / PDF 4 | DEFER-MISSING-PRECISE-STATEMENT | Same issue, with citation to Tisseur §2.3. **DEFERRED**. |

## Printed equation tags

| Tag | Location | Role | Evidence and status |
|---|---|---|---|
| (25.1) | p. 460 / PDF 2 | Exact Newton correction equation | `higham25NewtonEquation`, `higham25ExactNewtonStep`, implementation equivalence. **PASS**. |
| (25.2) | p. 460 / PDF 2 | Computed Newton iteration with three error sources | `Higham25RoundedNewtonStep` uses an exact perturbed solve and update, avoiding an unjustified total matrix inverse. **PASS**. |
| (25.3) | p. 461 / PDF 3 | Residual error budget | `higham25ResidualErrorBound`. **PASS**. |
| (25.4) | p. 461 / PDF 3 | Jacobian/solver error budget | `higham25JacobianErrorBound`. **PASS**. |
| (25.5) | p. 461 / PDF 3 | `u κ(J*) ≤ 1/8` | `higham25Eq25_5`. **PASS**. |
| (25.6) | p. 461 / PDF 3 | per-iterate solver smallness | `higham25Eq25_6`. **PASS**. |
| (25.7) | p. 461 / PDF 3 | initial-neighborhood smallness | `higham25Eq25_7`. **PASS**. |
| (25.8) | p. 461 / PDF 3 | approximate limiting relative accuracy | DEFER-MISSING-PRECISE-STATEMENT; undefined `≈` and stopping event. **DEFERRED**. |
| (25.9) | p. 462 / PDF 4 | approximate limiting residual | DEFER-MISSING-PRECISE-STATEMENT; undefined `≈` and stopping event. **DEFERRED**. |
| (25.10) | p. 463 / PDF 5 | eigenproblem as normalized nonlinear system | `higham25EigenResidual`, `higham25_eq25_10_zero_iff`. **PASS**. |
| (25.11) | p. 466 / PDF 8 | exact equality between the preceding limit-supremum condition number and the inverse-derivative norm formula | `higham25_eq25_11_of_implicitFunction` starts from `F(0,0)=0`, a `C¹` residual, its split derivative, and a continuous-linear equivalence for `F_x`. It produces the local unique solution map, proves derivative `-F_x⁻¹ F_d`, and proves the literal epsilon-indexed `sSup` tends to `‖F_x⁻¹ F_d‖ ‖d‖/‖x*‖`. **PASS**. |
| (25.12) | p. 466 / PDF 8 | Wozniakowski two-variable example | `higham25Eq25_12`, displayed positive solution, and exact zero theorem. **PASS**. |
| (25.13) | p. 466 / PDF 8 | floating-point evaluation of the example admits the displayed three-error representation | `higham25Eq25_13RoundedEval` fixes the straightforward operation order; `higham25_eq25_13_roundedEval_model` derives the two `u` witnesses and the common `gamma₃` quadratic-core witness from the primitive FP model, using `mu >= 0`. **PASS (EXPLICIT-DOMAIN)**. |
| (25.14) | p. 468 / PDF 10 | local quadratic-convergence premise | `higham25_eq25_14_denominator_bound` and `higham25_eq25_14_step_squared_bound` prove the printed stopping algebra with the source's “small enough” exposed as an exact reciprocal-square premise. **PASS (EXPLICIT-DOMAIN)**. |

## Other source content

| Content | Location | Decision | Status |
|---|---|---|---|
| Two-line Newton implementation after (25.1) | p. 460 / PDF 2 | FORMALIZE_CORE | Included in `higham25ExactNewtonStep`. **PASS**. |
| Addition-error bound after (25.4) | p. 461 / PDF 3 | FORMALIZE_CORE | `higham25AdditionErrorBound`. **PASS**. |
| Lipschitz Jacobian premise | p. 461 / PDF 3 | FORMALIZE_CORE | Accounted for in theorem-premise inventory; no named limit theorem is falsely asserted. |
| Iterative refinement special case | pp. 462-463 / PDFs 4-5 | FORMALIZE_CORE / CORE-PRECISE-PROSE | `higham25_linearSystem_newtonCorrection_iff_refinementCorrection` proves the exact Newton/refinement correction equivalence; `higham25_linearSystemJacobian_constant` and `higham25_linearSystemJacobian_lipschitz_zero` close the constant-Jacobian/`β=0` claim; `higham25_linearSystem_actualResidual_bridge_ch12` instantiates the actual `fl_residual` evaluator and the printed `γ_(n+1)` componentwise bound. The printed `F=b-Ax, J=A` has a sign inconsistency; Lean uses the correct derivative `J=-A`, whose sign cancels in the Newton equation. **PASS / SOURCE-DISCREPANCY**. |
| Linear-system condition specialization below (25.11) | p. 466 / PDF 8 | FORMALIZE_CORE / CORE-PRECISE-PROSE | `higham25_linearSystemDataDerivativeFrob_eq` proves `‖A⁻¹[x₁I … xₙI]‖_F=‖A⁻¹‖_F‖x‖₂`; `higham25_linearSystem_condition_frobenius` proves the printed relative condition identity `‖A⁻¹‖_F‖A‖_F`. **PASS**. |
| Eigenproblem bordered Jacobian, Lipschitz coefficient, simple-eigenvalue nonsingularity, and residual `ψ` formula | p. 463 / PDF 5, immediately after (25.10) | FORMALIZE_CORE / CORE-PRECISE-PROSE and CORE-SYMBOLIC-EXAMPLE | `higham25EigenJacobian`, `higham25EigenJacobian_mulVec_eq_action`, and the exact Taylor identities produce the displayed derivative. `higham25EigenJacobian_kernel_eq_zero_of_simple` proves nonsingularity from an explicit left/right/eigenspace certificate, but no theorem derives that certificate from a standard algebraic-multiplicity-one hypothesis. `higham25EigenRoundedResidual_error_bound` proves the literal primitive-operation evaluator satisfies (25.3) with `ψ = γ_(n+1)(‖A‖∞+|λ|)‖x‖∞`. `higham25EigenJacobian_source_lipschitz_counterexample` refutes the unqualified printed `2‖A‖` coefficient at `A=0`; `higham25EigenJacobian_lipschitz_two_inf` proves the corrected coefficient `2`. **PARTIAL / SOURCE-DISCREPANCY**. |
| Figure 25.1 / Frank-matrix MATLAB experiment | pp. 463-465 / PDFs 5-7 | EXCLUDED-EMPIRICAL | Accounted for; exact data and script are not printed. |
| First-order perturbation relation before (25.11) | pp. 464-466 / PDFs 6-8 | FORMALIZE_CORE | `higham25_eq25_11_first_order`. **PASS** for exact linearized algebra. |
| Sensitivity calculation and condition `1/2` after (25.13) | p. 466 / PDF 8 | FORMALIZE_CORE | `higham25_eq25_13_sensitivity_direction`, `higham25_eq25_13_condition_half`. **PASS**. |
| `μ=10^8` MATLAB experiment | p. 467 / PDF 9 | EXCLUDED-EMPIRICAL | Accounted for. |
| Implicit-function/Taylor derivation surrounding (25.11) | pp. 464-466 / PDFs 6-8 | FORMALIZE_CORE / CORE-PRECISE-PROSE | `higham25_isContDiffImplicitAt_of_partialEquiv` instantiates the IFT hypotheses; `higham25_implicitFunction_local_solution_contract` supplies local neighborhoods, existence, and uniqueness; `higham25_implicitFunction_hasFDerivAt` proves derivative `-F_x⁻¹ F_d`; and `higham25_eq25_11_of_implicitFunction` closes the literal condition-number limit. **PASS**. |
| Rheinboldt `C(F,S)` quotient and shrinking-set limit | p. 467 / PDF 9 | DEFER-MISSING-PRECISE-STATEMENT | The displayed max/min omits `u ≠ v`, nonemptiness, boundedness/compactness, positivity of the denominator, and attainment hypotheses; “closed” alone does not supply them. **DEFERRED**. |
| Rigorous residual/error factors `1/2` and `2` | p. 467 / PDF 9 | DEFER-MISSING-PRECISE-STATEMENT | The constants are printed, but the result says only “sufficiently close” and cites Kelley without specifying the differentiability, norm, or quantitative Taylor-remainder hypotheses needed for a theorem. **DEFERRED**. |
| §25.6 Notes and References | p. 468 / PDF 10 | EXCLUDED-BIBLIOGRAPHIC | Accounted for. |
| Problem 25.1 and (25.15) | p. 469 / PDF 11; Appendix pp. 569-570 | FORMALIZE-SUPPORTING-EXERCISE | `Higham25Problem25_1.lean` proves (A.15), fixed point, invariant ball, strict descent, geometric envelope, boundedness, and subsequential-limit bound. **PASS**. |
| Problem 25.1(c), practical explanation | p. 469 / PDF 11 | EXCLUDED-EXPOSITORY | Accounted for; no mathematical proposition is printed. |
| Problem 25.2, singular-Jacobian research problem | p. 469 / PDF 11 | EXCLUDED-RESEARCH | Accounted for. |

No mathematical footnote was found. The repeated download notice is not
chapter content.
