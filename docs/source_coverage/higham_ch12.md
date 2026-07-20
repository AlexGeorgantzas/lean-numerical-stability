# Higham Chapter 12 Formalization Report — "Iterative Refinement"

## Source and scope

- Edition: Nicholas J. Higham, *Accuracy and Stability of Numerical
  Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 12, "Iterative Refinement," printed pp. 231-243, PDF pages 1-14.
- Source: `References/1.9780898718027.ch12.pdf`, SHA-256
  `9aa86285b2a3e0bc6de4eaeadd63f40f479d3fdbeb319c43f7260a2f5e42a9b1`.
- Appendix: solutions 12.1-12.2, printed p. 556, in
  `References/1.9780898718027.appa.pdf`, SHA-256
  `8d4a7f7e99a95e19ad0f589342e287eca469453f448535b718c1f805115101a2`.
- Mode: core.
- Parallel split: 2 (Chapters 7-12).
- Planning documents consulted: complete parallel blueprint, complete Split 2
  primary contract, and Chapter 12 index row.
- Audited source count: four named results, 22 numbered equations, five
  Problems, two Appendix solution rows, three empirical tables, and the exact
  algorithm/definition/prose rows recorded in the inventory.
- Selected-scope gate: **PASS**.

The gate is deliberately narrower than a literal transcription. Theorems
12.1-12.2 use "approximately," `lesssim`, and "sufficiently less than 1"; the
sufficient-condition function in Theorem 12.4 is also approximate, and its
proof explicitly drops right-hand-side terms. Those envelopes are not claimed
as exact Lean theorems. The exact finite recurrence, Theorem 12.3 `q`
decomposition, correction/Neumann machinery, sigma bridge, conditional printed
conclusion, and solver-derived non-asymptotic stability companion are proved.

Primary Lean module:
`LeanFpAnalysis/FP/Algorithms/HighamChapter12.lean`; reusable refinement
infrastructure: `LeanFpAnalysis/FP/Algorithms/IterativeRefinement.lean`;
actual Chapter 9 solver handoff:
`LeanFpAnalysis/FP/Algorithms/HighamChapter12Ch9SolverBridge.lean`.

### Equation (12.6) / actual Chapter 9 solver bridge (2026-07-20 rerun)

The PDF states that Theorem 9.4 permits the concrete choice
`uW = gamma_(3n) |L_hat||U_hat|` in (12.6). Merely listing the Chapter 9
solver theorem beside the abstract (12.1) predicate did not compile that
composition. The new bridge closes it explicitly:

- `higham12_6_rectRoundedLoopW` is the displayed weight
  `3n/(1-3nu) |L_hat||U_hat|` for the literal rounded Doolittle factors;
- `higham12_6_u_mul_rectRoundedLoopW_eq` proves the exact (12.6) identity,
  including the valid `u = 0` case without dividing by `u`; and
- `higham12_6_rectRoundedLoop_lu_solve_SolverWBound_source` runs the actual
  rounded Doolittle loop and actual forward/back substitutions, consumes
  `higham9_4_rectRoundedLoop_square_lu_solve_backward_error_source`, and
  returns `higham12_1_SolverWBound` for the computed solution and concrete
  weight.

The public endpoint assumes only nonzero computed pivots and the two ordinary
`gammaValid` guards required by Theorem 9.4. It assumes no residual,
execution trace, perturbation, backward-error envelope, or solver-bound
conclusion.

## Progress snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 12 | core | 100 | 100 | 100 | 100 | 100 | 100 | 0 | none | high |

## Primary-label assessment

| Source label | Core decision | Lean evidence | Source-strength assessment |
|---|---|---|---|
| Theorem 12.1, mixed precision | Literal qualitative envelope excluded; exact core selected | `higham12_2_residual_delta_bound`, `higham12_5_forward_error_identity`, `higham12_5_forward_error_bound`, `higham12_forward_error_linear_contraction`, `higham12_forward_error_steady_state` | PASS for the exact recurrence/convergence core; no claim that "approximately eta" or "approximately u" has an invented exact meaning |
| Theorem 12.2, fixed precision | Literal qualitative envelope excluded; exact core selected | Same exact recurrence/contraction surface | PASS for the exact core; the printed `lesssim 2n cond(A,x)u` summary is not claimed literally |
| Theorem 12.3 / (12.10) | FORMALIZE_CORE | `higham12_10_exact_q_bound`, `higham12_3_exact_one_step_residual_bound`, `higham12_14_residual_identity`, `higham12_14_residual_bound` | PASS for the exact finite theorem and displayed `q`; the source's underparameterized `q = O(u)` interpretation is not strengthened |
| Theorem 12.4 / (12.22) | Precise conditional conclusion selected; approximate `f` envelope deferred | `higham12_4_conditional_two_gamma_bound`, `higham12_4_explicit_condition`, `higham12_4_from_solver`, `higham12_21_correction_infNorm_bound`, `higham12_22_infNorm_skew_apply` | PASS for exact companions. The conditional theorem exposes its dominance hypothesis; the solver-derived theorem proves `2 gamma_(n+1)(abs(A)abs(yhat)+abs(b))` and is not advertised as the literal sharper printed conclusion |

## Completed selected targets

| Source label | Lean declaration | File | Theorem surface | Notes |
|---|---|---|---|---|
| (12.1) | `higham12_1_SolverWBound` | `HighamChapter12.lean` | Abstract solver backward-error model | Source/model assumption |
| (12.2) | `higham12_2_residual_delta_bound` | `HighamChapter12.lean` | Exact componentwise residual-computation bound | Full source algebra |
| (12.4)-(12.5) | `higham12_5_forward_error_identity`, `higham12_5_forward_error_bound` | `HighamChapter12.lean` | Exact inverse-free one-step forward-error identity and bound | Avoids the source's `O(u^2)` inverse expansion |
| (12.6), Theorem 9.4 to (12.1) | `higham12_6_rectRoundedLoopW`, `higham12_6_u_mul_rectRoundedLoopW_eq`, `higham12_6_rectRoundedLoop_lu_solve_SolverWBound_source` | `HighamChapter12Ch9SolverBridge.lean` | Actual rounded Doolittle factors and triangular solves satisfy the Chapter 12 solver model with `uW = gamma_(3n)|L_hat||U_hat|` | No caller-supplied residual, execution, or backward-error certificate |
| (12.5) consequence | `higham12_forward_error_linear_contraction`, `higham12_forward_error_steady_state` | `HighamChapter12.lean` | Exact scalar affine recurrence and finite bound | Quantitative replacement for Theorems 12.1-12.2 summaries |
| (12.7)-(12.9) | `higham12_7_initialResidualBound`, `higham12_8_residualComputationBound`, `higham12_9_conventional_residual_error` | `HighamChapter12.lean` | Initial-solve and residual-computation models | (12.9) reuses the existing residual theorem |
| Theorem 12.3 / (12.10), (12.14) | `higham12_10_exact_q_bound`, `higham12_3_exact_one_step_residual_bound`, `higham12_14_residual_identity`, `higham12_14_residual_bound` | `HighamChapter12.lean` | Exact finite one-step residual theorem, including the displayed `q` decomposition | New audit wrapper closes the former (12.10)/(12.14) documentation mismatch |
| (12.17)-(12.21) | `higham12_17_update_bound`, `higham12_18_residual_abs_bound`, `higham12_19_combined_coefficients`, `higham12_21_correction_infNorm_bound` | `HighamChapter12.lean` | Exact update, residual, coefficient, and Neumann correction bounds | Printed approximate simplifications remain excluded |
| Theorem 12.4 / (12.22) | `higham12_4_conditional_two_gamma_bound`, `higham12_4_from_solver`, `higham12_22_infNorm_skew_apply` | `HighamChapter12.lean` | Exact conditional printed conclusion and fully solver-derived non-asymptotic `+ abs(b)` companion | Strength distinction is explicit in code and inventory |
| Problem/Appendix 12.1 | `higham12_problem_12_1_square` | `HighamChapter12.lean` | Square sigma/infinity-norm inequality used in (12.22) | Printed rectangular form is dimensionally inconsistent; square main-proof form proved |

## Reused from the repository or Mathlib

| Source concept/result | Existing declaration or module |
|---|---|
| Exact one-step refinement algebra and residual assembly | `IterativeRefinement.lean`: `one_step_refinement_error_identity`, `thm_11_3_*`, `eq_11_15`-`eq_11_18` |
| Conventional residual evaluation | `conventional_residual_error` |
| Affine contraction | `linear_contraction`, `linear_contraction_steady_state` |
| GE solve model for (12.6) | `higham9_4_rectRoundedLoop_square_lu_solve_backward_error_source`, composed by `higham12_6_rectRoundedLoop_lu_solve_SolverWBound_source` |
| GEPP power-of-two growth bound | Chapter 9 `higham9_7_*growthFactorEntry_le_pow_two*` surfaces |
| Finite sums, absolute values, extrema, and matrix norm infrastructure | Mathlib and existing `infNorm` compatibility layer |

The Chapter 12 wrapper now imports only `Mathlib.Tactic` and
`IterativeRefinement`; the unnecessary aggregate `HighamChapter11` import was
removed and the file compiles on that narrower dependency surface.

## New dependency and feasibility table

| Selected source target | Required foundation | Status | Existing source | Smallest local target | Downstream allowed? |
|---|---|---|---|---|---|
| Theorem 12.3 / (12.10) exact `q` form | Exact (12.14) residual assembly | available-local | `higham12_3_exact_one_step_residual_bound` | `higham12_10_exact_q_bound` | yes; implemented |
| Theorem 12.4 Neumann step | Nonnegative row-sum resolvent bound | available-local | `nonneg_resolvent_infNormVec_bound` | `higham12_21_correction_infNorm_bound` | yes; implemented |
| Theorem 12.4 sigma bridge | Finite max/min dominance | available-local | Problem/Appendix 12.1 | `higham12_22_infNorm_skew_apply` | yes; implemented |
| Literal Theorem 12.4 `f` envelope | Exact definition/bound for the printed approximate `f` and the terms discarded in the proof | out-of-scope-by-policy | source is explicitly approximate | retain exact companions and document the distinction | not a selected blocker |

No external literature or model oracle was used in this audit. The primary
chapter and Appendix proofs were sufficient; therefore no proof-source ledger
is triggered.

## Skipped, empirical, deferred, and benchmark categories

| Source location | Summary | Decision / reason code |
|---|---|---|
| Theorems 12.1-12.2 envelopes and estimates after (12.5) | Approximate contraction factors, limiting errors, and `lesssim` bounds | SKIP / SKIP-QUALITATIVE; exact cores proved |
| (12.3), (12.16), (12.18), and Theorem 12.4 `f` characterization | `O(u^2)`, dropped `b` terms, approximate gamma replacement, and approximate sufficient condition | DEFER / DEFER-MISSING-PRECISE-STATEMENT; exact finite companions proved |
| Tables 12.1-12.3 and surrounding "usually/typically/most tried" prose | GEPP/GE/QR outputs and observations | SKIP / SKIP-EMPIRICAL |
| §12.3 notes/history and §12.3.1 LAPACK catalogue/termination policy | Literature, named software, and implementation advice | SKIP-LITERATURE-REVIEW / SKIP-PROGRAMMING-LANGUAGE |
| Problem/Appendix 12.2 | Optional `cond(A,x)u` consequence with an unspecified multiple | SKIP-OPTIONAL-PROBLEM |
| Problem 12.3 | Empirical investigation | SKIP-EMPIRICAL |
| Problem 12.4 | Conventional-versus-fast multiplication refinement comparison | BENCHMARK-COMPARISON |
| Problem 12.5 | Open research problem for Cholesky and symmetric-indefinite solvers | SKIP-OPTIONAL-PROBLEM |

Detailed row-wise decisions, machine-detail omissions, and Appendix accounting
are in `docs/chapter12/CHAPTER12_SOURCE_INVENTORY.md`.

## Hidden-hypothesis audit

- `higham12_6_rectRoundedLoop_lu_solve_SolverWBound_source`: the literal
  rounded factors and triangular-solve outputs are definitions in the theorem
  conclusion. The only hypotheses are pivot nonbreakdown and `gammaValid`;
  the perturbation and its `uW` bound are constructed by the Chapter 9
  producer and the exact (12.6) coefficient identity.
- `higham12_10_exact_q_bound`: `hr`, `hy`, `hf1`, `hDeltaR`, and `hf2` are the
  source residual/solver/update assumptions. It assumes neither the residual
  conclusion nor the `q` rearrangement.
- `higham12_4_conditional_two_gamma_bound`: `hdom` is target-bearing
  dominance. The theorem is retained and named as conditional; it is not used
  to claim a solver-derived endpoint.
- `higham12_4_from_solver`: solver, residual, update, gamma-validity, and
  `u < 1` hypotheses are source/model-validity assumptions. The nonnegative
  `Ainv` resolver is an analysis-only stand-in for `abs(A^-1)`. The row-sum,
  lower-bound, and scalar inequalities are explicit non-asymptotic replacement
  conditions, not claims that automatically follow from the approximate
  source `f`.
- The solver-derived conclusion contains `+ abs(b)`. Code, inventory, and this
  report now agree that it is weaker than the literal printed conclusion and
  therefore an exact companion rather than a hidden closure of that source
  envelope.
- `higham12_problem_12_1_square` makes the source's dimension issue explicit;
  no rectangular theorem with mismatched vector dimensions is claimed.

## Weak-component audit

| Component | Why weak | First check | Fix/justification | Second independent check | Evidence | Status |
|---|---|---|---|---|---|---|
| Theorem 12.3 / (12.10) | Floating-point/asymptotic result | Lean type and proof compile | Added exact `q` wrapper rather than an unparameterized Big-O claim | Rendered pp. 235-236 algebra compared term-by-term | `higham12_10_exact_q_bound`; axiom audit | PASS |
| Conditional Theorem 12.4 | Target-bearing hypothesis | Lean type exposes `hdom` | Documentation labels it conditional | Rendered pp. 236-238 compared with theorem type | `higham12_4_conditional_two_gamma_bound` | PASS AS CONDITIONAL |
| Solver-derived Theorem 12.4 companion | Stability theorem with changed conclusion | Lean type shows `+ abs(b)` | Removed "complete/literal" overclaim | Rendered source has no `+ abs(b)` and approximate `f`; report records difference | `higham12_4_from_solver` | PASS AS EXACT COMPANION |
| Problem/Appendix 12.1 | Source dimension mismatch | Lean square type and proof | Retain only dimension-compatible form used by (12.22) | Rendered problem and Appendix solution checked | `higham12_problem_12_1_square` | PASS / SOURCE DISCREPANCY |
| Inventory/report gate | Completion claim | All four labels, 22 equations, five Problems checked against project index | Added fresh source-order inventory and per-row reasons | Entire rendered chapter and Appendix rows re-read | inventory plus this report | PASS |
| Import surface | Potential broad dependency | Removed `HighamChapter11` aggregate import | `IterativeRefinement` supplies all used declarations | Direct Lean compile on narrowed imports | focused compile | PASS |

No repeated blocker or red bottleneck remains.

## Verification

- Fresh (12.6) bridge checks (2026-07-20):
  `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter12Ch9SolverBridge.lean`
  and
  `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter12Ch9SolverBridge`
  both passed. `#print axioms` for
  `higham12_6_u_mul_rectRoundedLoopW_eq` and
  `higham12_6_rectRoundedLoop_lu_solve_SolverWBound_source` reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Fresh-worktree baseline:
  `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter12` — PASS, 3373 jobs.
  The only messages were pre-existing lints/deprecations in untouched
  `CholeskyFl.lean`, `HighamChapter9.lean`, and `HighamChapter10.lean`.
- Focused changed-file check:
  `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter12.lean` — PASS on
  the narrowed import surface.
- Focused target after the audit batch:
  `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter12` — PASS.
- Post-merge chapter-level aggregate gate:
  `lake build LeanFpAnalysis.FP` — PASS, 4315 jobs. The emitted diagnostics
  were pre-existing linter/deprecation warnings in untouched modules from
  Chapters 9-10, 14, 16, and 19-21, plus Cholesky, QR, matrix-power,
  FastMatMul, and test-matrix modules; no diagnostic came from Chapter 12.
- Public-surface consumer check: a minimal scratch consumer importing
  `LeanFpAnalysis.FP` and checking `higham12_10_exact_q_bound` and
  `higham12_4_from_solver` — PASS. The monolithic
  `examples/LibraryLookup.lean` reaches a process stack overflow while
  rendering its pre-existing thousands of `#check` messages, including with a
  64 MiB stack; this is an output-volume limitation, not a Chapter 12
  typechecking failure.
- Hygiene scan over the touched Chapter 12 Lean code found no `sorry`,
  `admit`, `axiom`, `unsafe`, or `opaque` placeholder.
- `#print axioms` for the exact Theorem 12.3 wrapper, contraction theorem,
  conditional and solver-derived Theorem 12.4 companions, and sigma bridge
  reported only `propext`, `Classical.choice`, and `Quot.sound` where used.
- `git diff --check` — PASS.

## Documentation and open issues

- Inventory: `docs/chapter12/CHAPTER12_SOURCE_INVENTORY.md`.
- Decision report: `docs/source_coverage/higham_ch12.md`.
- Not-proved/proof-source/bottleneck ledgers: not triggered; zero selected rows
  remain open.
- Public navigation: `docs/LIBRARY_LOOKUP.md` and
  `examples/LibraryLookup.lean` include the audited source-facing endpoints.
- Source discrepancy: the literal rectangular statement of Problem 12.1 is
  dimensionally inconsistent; the square instance used in the main proof and
  Appendix derivation is the proved target.
- Planning discrepancy: the local Split 2 Appendix ownership list omits
  solutions 12.1-12.2 even though the rendered Appendix contains both. This
  tracked report/inventory records the source-authoritative correction without
  staging local-only `chapter_splitting/` artifacts.

There are no open selected-scope items in default core mode.
