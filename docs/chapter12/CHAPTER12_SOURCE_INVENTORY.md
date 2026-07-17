# Higham Chapter 12 Source Inventory

## Audit basis

- Audit date: 2026-07-17.
- Book: Nicholas J. Higham, *Accuracy and Stability of Numerical Algorithms*,
  2nd ed. (SIAM, 2002), as identified by the repository metadata and the
  Chapter 12 numbering.
- Primary source: `References/1.9780898718027.ch12.pdf`, SHA-256
  `9aa86285b2a3e0bc6de4eaeadd63f40f479d3fdbeb319c43f7260a2f5e42a9b1`.
- Chapter: 12, "Iterative Refinement," printed pp. 231-243, PDF pages 1-14.
- Appendix source: `References/1.9780898718027.appa.pdf`, SHA-256
  `8d4a7f7e99a95e19ad0f589342e287eca469453f448535b718c1f805115101a2`;
  Chapter 12 solutions 12.1-12.2 are on printed p. 556.
- Mode: core; parallel owner: Split 2.
- Planning documents consulted: the complete parallel blueprint, the complete
  Split 2 primary-contract section, and the Chapter 12 index row.
- Inspection: every chapter page, all 22 numbered equations, all four named
  results, all five Problems, both Appendix solution rows, extracted text, and
  rendered checks of printed pp. 232-238 and 242-243.
- Planning correction: the Split 2 Appendix ownership list omits solutions
  12.1-12.2, but the rendered Appendix contains both. They are inventoried here
  under Chapter 12 / Split 2 ownership; this does not make unselected Problems
  mandatory in core mode.

The selected-scope gate is **PASS**. Literal claims containing `approximately`,
`lesssim`, `O(u)` without a parameterized asymptotic setup, or an approximate
sufficient-condition function are not presented as exact Lean theorems. Their
exact finite algebraic cores and stability companions are selected and proved.

## Source-order inventory

| ID | Source location | Kind | Statement summary | Precision | Generality | Source proof | Dependencies | Decision | Reason code | Lean artifact/status |
|---|---|---|---|---|---|---|---|---|---|---|
| 12.B1 | p. 232 / PDF 2 | Algorithm semantics | Compute residual, solve the correction equation, and update the iterate; in exact arithmetic one step returns the exact solution | precise | general | explanatory | matrix algebra | REUSE_EXISTING | REUSE-REPOSITORY | `one_step_refinement_error_identity`, `higham12_5_forward_error_identity`; PASS |
| (12.1) | p. 232 / PDF 2 | Solver model | `(A + DeltaA)y = c`, with componentwise `abs DeltaA <= u W` and `W` independent of the right-hand side | precise | general | model assumption | earlier solver analysis | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham12_1_SolverWBound`; PASS |
| (12.2) | p. 233 / PDF 3 | Residual bound | Exact componentwise residual-computation error bound after `x_i = x + (x_i-x)` | precise | general | complete derivation | (3.11), exact solve | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham12_2_residual_delta_bound`; PASS |
| (12.3) | p. 233 / PDF 3 | Solver-inverse estimate | `abs F_i <= u abs(A^-1) W + O(u^2)` | partly precise | general/asymptotic | sketch | Neumann expansion | DEFER | DEFER-MISSING-PRECISE-STATEMENT | Literal `O(u^2)` envelope deferred; exact resolver/Neumann replacements are `correction_neumann_inequality` and `higham12_21_correction_infNorm_bound` |
| (12.4) | p. 233 / PDF 3 | Correction identity | Express the computed correction through the perturbed solve and the residual error | precise | general | complete derivation | (12.1), inverse algebra | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Inverse-free exact equivalent `higham12_5_forward_error_identity`; PASS |
| (12.5) | p. 233 / PDF 3 | Forward-error recurrence | Componentwise affine recurrence `abs(x_{i+1}-x) <= G_i abs(x-x_i) + g_i` | precise core plus approximate estimates | general | complete core derivation | (12.2)-(12.4), rounded update | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham12_5_forward_error_bound`, `higham12_forward_error_linear_contraction`, `higham12_forward_error_steady_state`; PASS for the exact core; following `approximately/lesssim` estimates excluded |
| T12.1 | p. 234 / PDF 4 | Named theorem | Mixed-precision refinement reduces forward error by a factor approximately `eta` until relative error is approximately `u` | underspecified | general | summary of preceding analysis | (12.1)-(12.5) | SKIP | SKIP-QUALITATIVE | Literal envelope is not claimed; exact recurrence and geometric consequence above are PASS |
| (12.6) | p. 234 / PDF 4 | LU specialization | GE solver model `uW` represented by `gamma_(3n) abs(Lhat) abs(Uhat)` | precise model specialization | general | reuse of Theorem 9.4 | Chapter 9 GE analysis | REUSE_EXISTING | REUSE-REPOSITORY | Chapter 9 `higham9_4_*` surfaces; PASS |
| T12.2 | p. 234 / PDF 4 | Named theorem | Fixed-precision refinement reduces forward error approximately by `eta` until a `lesssim 2n cond(A,x)u` envelope | underspecified | general | summary of preceding analysis | (12.1)-(12.5) | SKIP | SKIP-QUALITATIVE | Literal envelope is not claimed; exact contraction skeleton is PASS |
| (12.7) | p. 235 / PDF 5 | Initial-solve model | Componentwise initial residual is bounded by `u(g(A,b) abs(xhat) + h(A,b))` | precise | general | assumption | solver specification | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham12_7_initialResidualBound`; PASS |
| (12.8) | p. 235 / PDF 5 | Residual model | Computed residual error is bounded by `u t(A,b,xhat)` | precise | general | assumption | residual computation | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham12_8_residualComputationBound`; PASS |
| (12.9) | p. 235 / PDF 5 | Conventional residual | Conventional residual evaluation has the `gamma_(n+1)(abs(A)abs(xhat)+abs(b))` envelope | precise | general | reuse of (3.11) | dot product/residual FP model | REUSE_EXISTING | REUSE-REPOSITORY | `higham12_9_conventional_residual_error`; PASS |
| T12.3 / (12.10) | pp. 235-236 / PDFs 5-6 | Named theorem / bound | One refinement step satisfies the displayed residual bound, with an explicit finite `q`; the source interprets `q = O(u)` under an informal parameterized regularity condition | precise finite core; partly precise asymptotic tail | general | complete | (12.7)-(12.9), (12.11)-(12.14) | FORMALIZE_CORE | CORE-NAMED-RESULT | `higham12_10_exact_q_bound` and `higham12_3_exact_one_step_residual_bound`; PASS for the exact finite theorem; no stronger Big-O claim |
| (12.11) | p. 236 / PDF 6 | Proof equation | Initial exact residual inherits (12.7) | precise | general | complete | (12.7) | FORMALIZE_DEPENDENCY | DEP-REQUIRED | Hypothesis instantiated in `higham12_3_exact_one_step_residual_bound`; PASS proof-internal |
| (12.12) | p. 236 / PDF 6 | Proof equation | Computed correction satisfies the solver residual/error model | precise | general | complete | (12.7) with right-hand side `rhat` | FORMALIZE_DEPENDENCY | DEP-REQUIRED | `hf1` surface in the Theorem 12.3 wrappers; PASS proof-internal |
| (12.13) | p. 236 / PDF 6 | Update model | Rounded update `yhat = xhat + dhat + f2`, `abs f2 <= u(abs xhat + abs dhat)` | precise | general | FP model assumption | rounded addition | FORMALIZE_DEPENDENCY | DEP-REQUIRED | `hy`/`hf2` surfaces in the Theorem 12.3/12.4 wrappers and `higham12_17_update_bound`; PASS |
| (12.14) | p. 236 / PDF 6 | Residual identity/bound | Exact assembled residual identity, triangle bound, and explicit `q` decomposition | precise | general | complete | (12.11)-(12.13) | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham12_14_residual_identity`, `higham12_14_residual_bound`, `higham12_10_exact_q_bound`; PASS |
| 12.D1 | p. 236 / PDF 6 | Definition | Ill-scaling `sigma(B,x)` is the max/min ratio of components of `abs(B)abs(x)` | precise on positive/nonempty domain | general | definition | finite extrema | FORMALIZE_DEPENDENCY | DEP-REQUIRED | `higham12_vectorAbsSkew` plus positivity lemmas; PASS with explicit domain |
| T12.4.precise | pp. 236-238 / PDFs 6-8 | Named theorem, precise component | Under an exact dominance condition, one step has componentwise residual at most `2 gamma_(n+1) abs(A)abs(yhat)` | precise conclusion | general | asymptotic proof | (12.14)-(12.22), sigma bridge | FORMALIZE_CORE | CORE-NAMED-RESULT | `higham12_4_conditional_two_gamma_bound`; PASS as an explicitly conditional exact theorem |
| T12.4.envelope | pp. 236-238 / PDFs 6-8 | Named theorem, approximate condition | Existence of `f(t1,t2)` approximately equal to a displayed formula, with source proof dropping `b` terms and replacing `gamma_(n+1)+u` approximately | underspecified | general/asymptotic | sketch with explicit approximations | exact solver/residual/update bounds | DEFER | DEFER-MISSING-PRECISE-STATEMENT | Not claimed literally; solver-derived exact companion `higham12_4_from_solver` proves `2 gamma_(n+1)(abs(A)abs(yhat)+abs(b))` under visible non-asymptotic conditions |
| (12.15) | p. 237 / PDF 7 | Proof inequality | Exact residual assembly before the source's simplifying approximations | precise | general | complete | (12.9), (12.14) | FORMALIZE_DEPENDENCY | DEP-REQUIRED | Exact assembly is supplied by `higham12_14_residual_bound` and `higham12_19_combined_coefficients`; PASS proof-internal |
| (12.16) | p. 237 / PDF 7 | Simplified estimate | Replace `b` by zero and approximate `gamma_(n+1)+u` by `gamma_(n+1)` | underspecified | asymptotic | heuristic simplification | (12.15) | SKIP | SKIP-QUALITATIVE | Exact unsimplified residual companions retained; no equality is invented |
| (12.17) | p. 237 / PDF 7 | Update inequality | Exact bound for `abs(xhat)` followed by an approximate simplification | precise finite inequality plus approximation | general | complete | (12.13) | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham12_17_update_bound`, `higham12_17_update_bound_div`; PASS for the exact inequality |
| (12.18) | p. 237 / PDF 7 | Residual estimate | Bound `abs(rhat)` after dropping right-hand-side terms and using (12.17) | partly precise | general/asymptotic | derivation with dropped terms | (12.7), (12.9), (12.17) | DEFER | DEFER-MISSING-PRECISE-STATEMENT | Exact no-drop replacement `higham12_18_residual_abs_bound`; PASS as companion, not literal display |
| (12.19) | p. 237 / PDF 7 | Coefficient assembly | Separate the corrected residual into `M1 abs(A)abs(yhat)` and `M2 abs(A)abs(dhat)` terms | precise conditional core | general | complete after (12.16) | (12.16)-(12.18) | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham12_19_combined_coefficients`; PASS for exact assembled coefficients under explicit models |
| (12.20) | p. 238 / PDF 8 | Correction inequality | Rearranged nonnegative correction inequality `(I-uM3)abs(A)abs(dhat) <= ...` | precise | general | complete | perturbed correction solve | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `correction_neumann_inequality`, `higham12_20_correction_via_resolver`; PASS |
| (12.21) | p. 238 / PDF 8 | Neumann bound | Under row-sum contraction, solve the correction inequality with inverse norm bounded by `2` | precise after explicit threshold | general | complete | (12.20) | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham12_21_correction_infNorm_bound`, `higham12_21_correction_product_bound`; PASS |
| (12.22) | p. 238 / PDF 8 | Final residual/sigma bound | Apply the correction bound and sigma bridge to obtain the final coefficient inequality | precise core; approximate final estimate follows | general | complete core | (12.19)-(12.21), Problem 12.1 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham12_22_infNorm_skew_apply`, `higham12_4_conditional_two_gamma_bound`; PASS for exact core |
| 12.B2 | p. 239 / PDF 9 | Precise prose reuse | GEPP growth factor is bounded by a power of two | precise | general | cross-reference | Chapter 9 | REUSE_EXISTING | REUSE-REPOSITORY | `higham9_7_partialPivot_growthFactorEntry_le_pow_two_of_stage_bounds` and trace-level variants; PASS |
| 12.B3 | pp. 239-240 / PDFs 9-10 | Experiment | Tables 12.1-12.3 compare GEPP, unpivoted GE, and QR on three named matrices with a random right-hand side | empirical run | fixed machine computation | observed output | implementations, random seed, stopping behavior | SKIP | SKIP-EMPIRICAL | Tables not encoded; exact backward-error mechanisms selected separately |
| 12.B4 | pp. 240-242 / PDFs 10-12 | Notes/history | Literature survey, historical implementations, qualitative convergence advice, condition estimate, and fault-tolerance discussion | editorial/qualitative | editorial | citations/observation | later chapters | SKIP | SKIP-LITERATURE-REVIEW | Accounted; no Lean target |
| 12.B5 | pp. 241-242 / PDFs 11-12 | LAPACK/software | xGESVX/xGERFS routine catalogue and three implementation termination criteria | precise software policy but implementation-specific | named software | documentation | LAPACK semantics | SKIP | SKIP-PROGRAMMING-LANGUAGE | Not selected in mathematical core mode |
| P12.1 / A12.1 | p. 242 / PDF 12; Appendix p. 556 | Problem and solution | Sigma/max-min dominance inequality used by (12.22) | precise only in the square use; printed rectangular form is dimensionally inconsistent | square symbolic dependency | complete Appendix solution | finite max/min and infinity norm | FORMALIZE_DEPENDENCY | CORE-PROBLEM-SELECTED | `higham12_problem_12_1_square`; PASS for the dimension-compatible main-proof form; discrepancy documented |
| P12.2 / A12.2 | p. 242 / PDF 12; Appendix p. 556 | Optional Problem and solution | Derive a `cond(A,x)u` forward bound for GEPP after one fixed-precision refinement step | partly precise (`bounded by a multiple`) | GEPP | sketch in Appendix | (12.5), Theorem 12.4, Problem 12.1 | SKIP | SKIP-OPTIONAL-PROBLEM | Not selected; exact contraction infrastructure is reusable but no claim of this unspecified multiple |
| P12.3 | p. 242 / PDF 12 | Optional empirical Problem | Investigate empirically `norm(abs(L)abs(L^-1))` for GEPP | empirical | experiments | none | GEPP implementation/data | SKIP | SKIP-EMPIRICAL | Not selected |
| P12.4 | p. 242 / PDF 12 | Optional comparison Problem | Parallel multiple-RHS refinement with conventional residual multiplication and fast correction multiplication satisfying Chapter 13 (13.4) | partly precise/cross-chapter | method comparison | none | Chapter 13 fast product model | BENCHMARK_CANDIDATE | BENCHMARK-COMPARISON | Reserved for benchmark/comprehensive work |
| P12.5 | pp. 242-243 / PDFs 12-13 | Research Problem | Ask whether one refinement step suffices for Cholesky and symmetric-indefinite pivoting under a condition bound | open research question | two solver families | none | Chapters 10-11 | SKIP | SKIP-OPTIONAL-PROBLEM | Not selected; no theorem stub |

## Empirical-output audit

| Source location | Printed claim/output | Missing execution details | Precise replacement | Status |
|---|---|---|---|---|
| Tables 12.1-12.3, pp. 239-240 | Backward-error sequences for `orthog(25)`, `clement(50)`, and `gfpp(50)` under GEPP, GE, and QR | Machine, arithmetic format, compiler, BLAS/LAPACK versions, random seed/vector, exact program, and exceptional behavior | Exact residual, correction, contraction, and stability theorems | EXCLUDED EMPIRICAL |
| p. 239 surrounding prose | "Usually," "typically O(n)," convergence in most tried examples | Dataset and experiment protocol | Power-of-two GEPP bound reused; exact stability companions proved | QUALITATIVE/EMPIRICAL EXCLUDED |

## Completion accounting

- Named results: all four inventoried. The exact cores of Theorems 12.3-12.4
  are selected and proved; the explicitly approximate summaries/envelopes of
  Theorems 12.1-12.2 and the approximate `f` clause of Theorem 12.4 are
  excluded or deferred without being strengthened into invented mathematics.
- Numbered equations: all 22 inventoried; every selected exact equation has a
  proved declaration, proof-internal representation, or recorded repository
  reuse.
- Optional Problems: Problem/Appendix 12.1 is selected as a dependency and
  proved in the dimension-compatible square form used by (12.22). Problems
  12.2-12.5 and Appendix solution 12.2 are individually accounted for and are
  not core blockers.
- No selected row is open; no not-proved, proof-source, or bottleneck ledger is
  triggered for Chapter 12 after this audit.
