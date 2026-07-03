# Higham Chapter 17 Source Coverage Ledger

## Source and Scope

- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002), verified from the chapter PDF metadata and rendered chapter title.
- Chapter: 17, "Stationary Iterative Methods".
- Printed pages: 321-337.
- Source file: `References/1.9780898718027.ch17.pdf`.
- Mode: core.
- Parallel split: 3B.
- Planning documents consulted: `chapter_splitting/HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md`, the Split 3B section of `chapter_splitting/split_primary_contracts.md`, and the Chapter 17 rows of `chapter_splitting/chapter_index.md`.
- Selected-scope gate: FAIL. The existing `StationaryIteration.lean` module proves several nonsingular stationary-iteration algebra, forward-error, Jacobi/SOR, and residual-bound dependencies, including the source-sign computed finite-sum identity for (17.3), the exact fixed-point/finite-sum solution identity for (17.4), the finite-sum error recurrence for (17.5), the finite-sum residual recurrence for (17.18), and a finite sigma-form residual bound for (17.19), and this ledger records the correct 2nd-edition Chapter 17 numbering. The full selected core pass remains open for infinite-sum statements, gamma/theta supremum definitions, diagonalizable sigma bounds, singular-system Drazin/semiconvergence analysis, and stopping-test equivalences imported from Chapter 7.

## Progress Snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| ch17 | core | 100 | 80 | 66 | 58 | 82 | 60 | 18+ | Infinite-sum bounds, diagonalizable residual sigma forms, and singular-system foundations are not yet formalized; current proofs cover nonsingular computed/exact/error/residual finite-sum algebra, finite sigma/q-bound residuals, finite/q-bound forward dependencies, and source-label repair | medium-low |

## Completed Selected Targets

| Source label | Lean declaration | File | Theorem surface | Notes |
|---|---|---|---|---|
| stationary splitting setup | `SplittingSpec`, `iterMatrix`, `dualIterMatrix` | `LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean` | Structure/definitions | Models `A = M - N`, `G = M^{-1}N`, and `H = NM^{-1}` in the repository's finite function-shaped matrix API. |
| (17.1), source sign | `SourceComputedIteration`, `computedIteration_of_sourceComputedIteration` | `StationaryIteration.lean` | Structure/theorem | Adds the source-sign convention `M xhat_{k+1} = N xhat_k + b - xi_k` and bridges it to the legacy internal `+ xi_k` convention by negating the local error term. |
| (17.3), computed finite-sum recurrence | `sourceComputedIteration_step_affine`, `sourceComputedIteration_finite_sum` | `StationaryIteration.lean` | Theorems | Applies the left-inverse certificate for `M` to (17.1), then unrolls the time-varying affine recurrence to the source-sign finite-sum formula. |
| one-step error dependency | `one_step_error`, `one_step_error_source` | `StationaryIteration.lean` | Theorems | Proves the one-step error recurrence for the legacy and source-sign conventions; this is dependency infrastructure for (17.5). |
| (17.4), exact solution recurrence | `stationary_solution_fixed_point`, `stationary_solution_finite_sum` | `StationaryIteration.lean` | Theorems | Proves that an exact solution of `Ax=b` is a fixed point of `x ↦ Gx + M^{-1}b`, then unrolls that affine fixed point into the finite-sum identity for (17.4). |
| (17.5), finite-sum error recurrence | `sourceComputedIteration_error_finite_sum` | `StationaryIteration.lean` | Theorem | Unrolls the source-sign one-step error recurrence to the finite-sum error identity with source term `M^{-1} xi`. |
| (17.2) | `LocalErrorBound` | `StationaryIteration.lean` | Predicate | Local componentwise rounding-error budget for the internal signed error. |
| (17.6), partial | `componentwise_forward_bound` | `StationaryIteration.lean` | Theorem | Triangle-inequality componentwise finite-sum bound; full source infinite-sum closure remains open. |
| (17.8), q-bound corollary | `normwise_forward_bound` | `StationaryIteration.lean` | Theorem | Finite q-contraction version of the normwise forward bound under `||G||_inf <= q < 1` and a uniform local-error bound. |
| (17.10) | `local_error_simplified` | `StationaryIteration.lean` | Theorem | Simplifies the local error budget using a supplied componentwise iterate bound. |
| (17.12), finite certificate | `PartialSumBound` | `StationaryIteration.lean` | Predicate | Finite partial-sum version of the `c(A)` comparison; the literal infinite/minimum source definition remains open. |
| (17.13), finite certificate form | `main_forward_bound` | `StationaryIteration.lean` | Theorem | Composes the finite componentwise bound, local-error simplification, and partial-sum certificate. |
| (17.16), Jacobi specialization | `jacobi_splitting_abs` | `StationaryIteration.lean` | Theorem | Proves the absolute splitting identity for Jacobi's method. |
| (17.17), SOR specialization | `sor_splitting_bound` | `StationaryIteration.lean` | Theorem | Proves the source SOR componentwise splitting factor under the explicit diagonal/lower/upper decomposition hypotheses. |
| (17.18), residual recurrence | `AG_eq_HA`, `A_matPow_G_eq_matPow_H_A`, `A_matMul_Minv_eq_sub`, `one_step_residual`, `residual_finite_sum` | `StationaryIteration.lean` | Theorems | Proves the algebra behind the residual recurrence, the one-step residual form, and the finite-sum residual recurrence `r_{m+1} = H^(m+1) r_0 - sum H^k (I-H) xi_{m-k}`. |
| (17.19), sigma/q-bound residual corollaries | `normwise_residual_sigma_finite_bound`, `sigma_bound`, `normwise_one_step_residual_bound`, `normwise_residual_bound` | `StationaryIteration.lean` | Theorems | Proves the finite sigma-form normwise residual bound from `residual_finite_sum`, plus a geometric q-bound on the sigma sum and the corresponding q-style normwise residual bound. |

## Source Inventory

| ID | Source location | Kind | Statement summary | Precision | Generality | Source proof | Dependencies | Decision | Reason code | Lean artifact/status |
|---|---|---|---|---|---|---|---|---|---|---|
| H17.Setup.stationary_iteration | p.325, Section 17.2 | definition | Stationary method `M x_{k+1} = N x_k + b`, `A = M - N`, with `M` nonsingular and `G = M^{-1}N`. | precise | nonsingular square | not applicable | matrix product/inverse certificate | FORMALIZE_CORE | DEP-REQUIRED | `SplittingSpec`, `iterMatrix`; spectral-radius convergence assumption not yet modeled. |
| H17.Eq17_1.computed_iteration | p.325, (17.1) | equation/model | Computed stationary iteration with a signed local error term. | precise | square current API | model assumption | splitting setup | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `SourceComputedIteration`; internal legacy bridge via `computedIteration_of_sourceComputedIteration`. |
| H17.Eq17_2.local_error_bound | p.325, (17.2) | inequality/model | Componentwise local error budget in terms of `|M|`, `|N|`, current iterates, and `|b|`. | precise | triangular `M` model | sketch/model | FP local-error model | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `LocalErrorBound`; exact triangular-solve derivation not modeled. |
| H17.Eq17_3.iterate_solution | p.325, (17.3) | recurrence | Closed-form computed iterate recurrence from (17.1). | precise | finite m | algebra | H17.Eq17_1 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `sourceComputedIteration_step_affine` and `sourceComputedIteration_finite_sum`; source-sign finite-sum recurrence closed. |
| H17.Eq17_4.stationary_exact_solution | p.325, (17.4) | recurrence | Exact stationary solution identity using the same finite sum. | precise | nonsingular square | algebra | splitting setup | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `stationary_solution_fixed_point` and `stationary_solution_finite_sum`; exact finite-sum side closed. |
| H17.Eq17_5.error_recurrence | p.325, (17.5) | recurrence | Error recurrence obtained by subtracting (17.3) and (17.4). | precise | finite m | algebra | H17.Eq17_3, H17.Eq17_4 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `sourceComputedIteration_error_finite_sum`; source-sign finite-sum error recurrence closed via the one-step error recurrence. |
| H17.Eq17_6.componentwise_forward_bound | p.325, (17.6) | inequality | Componentwise finite-sum forward-error bound. | precise | finite m | triangle inequality | H17.Eq17_5 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Partial finite triangle wrapper `componentwise_forward_bound`. |
| H17.Eq17_7.gamma_x | p.326, (17.7) | definition | Supremum ratio bounding the norm of computed iterates relative to the exact solution. | precise | normwise | not applicable | iterate sequence | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open; currently represented only by explicit hypotheses in downstream theorems. |
| H17.Eq17_8.normwise_forward_bound | p.326, (17.8) | inequality | Normwise forward-error bound with an infinite sum of `||G^k M^{-1}||_inf`. | precise | nonsingular square | norm bound | H17.Eq17_6, H17.Eq17_7 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Partial q-bound corollary: `normwise_forward_bound`; literal infinite-sum version open. |
| H17.Eq17_9.theta_x | p.326, (17.9) | definition | Supremum componentwise ratio bounding all computed iterates by the exact solution. | precise with zero-component caveat | componentwise | not applicable | iterate sequence | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open; current `local_error_simplified` takes the bound as a hypothesis. |
| H17.Eq17_10.local_error_simplified | p.326, (17.10) | inequality | Local error simplified using the componentwise iterate bound. | precise | componentwise | algebra/sketch | H17.Eq17_2, H17.Eq17_9 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `local_error_simplified`. |
| H17.Eq17_11.infinite_componentwise_bound | p.326, (17.11) | inequality | Infinite-sum componentwise forward-error bound. | precise | nonsingular square | algebra | H17.Eq17_6, H17.Eq17_10 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open; finite/certificate version is part of `main_forward_bound`. |
| H17.Eq17_12.cA_definition | p.326, (17.12) | definition | `c(A)` as a minimum comparison between an infinite nonnegative matrix sum and `|A^{-1}|`. | precise | nonsingular square | definition | infinite series convergence | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Partial finite predicate `PartialSumBound`; literal infinite/minimum definition open. |
| H17.Eq17_13.main_componentwise_bound | p.327, (17.13) | inequality | Main componentwise forward-error bound in terms of `c(A)`, `|A^{-1}|`, `|M|+|N|`, and `|x|`. | precise | nonsingular square | follows from (17.11)-(17.12) | H17.Eq17_11, H17.Eq17_12 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Partial finite/certificate theorem `main_forward_bound`. |
| H17.ScaleIndependence | p.327, prose | precise prose | Row/column diagonal scaling preserves the eigenvalues of `M^{-1}N` under elementwise-compatible splittings. | precise but needs matrix-similarity setup | Jacobi/SOR-like splittings | sketch | diagonal scaling, spectrum | FORMALIZE_CORE | CORE-PRECISE-PROSE | Open. |
| H17.Eq17_14.cA_heuristic_lower | p.327, (17.14) | heuristic inequality | Heuristic eigenvalue lower-bound indicator for `c(A)`. | partly precise | diagonalizable intuition | explanatory | spectral decomposition | SKIP | SKIP-QUALITATIVE | Not encoded in core; exact diagonal case may be a future dependency if needed. |
| H17.Eq17_15.norm_form_corollary | p.328, (17.15) | inequality | Infinity-norm form of the componentwise bound. | precise | nonsingular square | follows from (17.13) | H17.Eq17_13 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open. |
| H17.Eq17_16.jacobi_bound | p.328, (17.16) | inequality/corollary | Jacobi specialization of the main componentwise forward-error bound. | precise | Jacobi method | follows from (17.15) | H17.Eq17_15, Jacobi splitting | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Partial dependency `jacobi_splitting_abs`; full bound open. |
| H17.Eq17_17.sor_splitting_factor | p.329, (17.17) | inequality | SOR componentwise splitting factor `(1 + |1 - omega|) / omega`. | precise | SOR method | algebra | diagonal/lower/upper split | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `sor_splitting_bound`; downstream SOR forward bound open. |
| H17.Eq17_18.residual_recurrence | p.330, (17.18) | recurrence | Residual recurrence using `H = NM^{-1}` and `(I-H)xi`. | precise | nonsingular square | algebra | `AG = HA`, `AM^{-1} = I-H` | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `residual_finite_sum`, supported by `AG_eq_HA`, `A_matPow_G_eq_matPow_H_A`, `A_matMul_Minv_eq_sub`, and `one_step_residual`; finite-sum recurrence closed. |
| H17.Eq17_19.normwise_residual_bound | p.330, (17.19) | inequality | Normwise residual bound using sigma. | precise | nonsingular square | norm bound | H17.Eq17_18 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `normwise_residual_sigma_finite_bound` proves the finite sigma-form bound; `sigma_bound` and `normwise_residual_bound` provide q-style corollaries. |
| H17.Eq17_20.diagonalizable_sigma_bound | p.330, (17.20) | inequality | Diagonalizable `H` sigma bound with eigenvector conditioning and eigenvalues. | precise | diagonalizable | sketch | eigendecomposition/spectrum | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open. |
| H17.Eq17_21.singular_exact_iterate | p.332, (17.21) | recurrence | Exact stationary iterate recurrence for singular consistent systems. | precise | singular square | algebra | splitting setup | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open. |
| H17.Eq17_22.semiconvergent_form | p.332, (17.22) | decomposition | Semiconvergent `G` block form. | precise | singular square | cited lemma | Jordan/decomposition theory | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open; missing semiconvergence/Jordan foundation. |
| H17.Eq17_23.I_minus_G_form | p.332, (17.23) | decomposition | Block form for `I-G`. | precise | singular square | follows from (17.22) | H17.Eq17_22 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open. |
| H17.Eq17_24.Drazin_form | p.332, (17.24) | definition/decomposition | Drazin inverse representation for `I-G`. | precise | index-one singular setup | cited/background | Drazin inverse | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open; Drazin inverse absent locally. |
| H17.Eq17_25.limit_G_pow | p.332, (17.25) | limit identity | Limit of `G^m` in terms of `(I-G)^D`. | precise | semiconvergent | follows from (17.22)-(17.24) | matrix powers, Drazin | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open. |
| H17.Eq17_26.singular_limit_solution | p.333, (17.26) | limit formula | Limit solution for singular stationary iteration depending on `x0`. | precise | consistent singular systems | algebra | H17.Eq17_25 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open. |
| H17.Eq17_27.singular_error_split | p.334, (17.27) | recurrence | Singular-system error split into range and null components. | precise | semiconvergent singular systems | algebra | H17.Eq17_26, splitting projector `E` | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open. |
| H17.Eq17_28.Sm_definition | p.334, (17.28) | definition | Source term `S_m` for the singular-system forward-error analysis. | precise | singular systems | not applicable | H17.Eq17_27 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open. |
| H17.Eq17_29.singular_Sm_bounds | p.334, (17.29) | inequalities | Normwise and componentwise bounds on `S_m`. | precise | singular systems | norm/componentwise bound | H17.Eq17_28, H17.Eq17_2 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open. |
| H17.Eq17_30.GiE_decomposition | p.334, (17.30) | decomposition | Block computation showing convergence of sums involving `G^i E`. | precise | semiconvergent singular systems | algebra | H17.Eq17_22-H17.Eq17_24 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open. |
| H17.Eq17_31.singular_normwise_bound | p.334, (17.31) | inequality | Singular-system normwise forward-error bound. | precise | semiconvergent singular systems | follows from (17.29)-(17.30) | singular foundations | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open. |
| H17.Eq17_32.singular_componentwise_bound | p.335, (17.32) | inequality | Singular-system componentwise forward-error bound with linear null-component term. | precise | semiconvergent singular systems | follows from (17.29)-(17.30) | singular foundations | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open. |
| H17.Eq17_33a.stop_rhs_backward | p.336, (17.33a) | equivalence | Residual stopping test equivalent to perturbing `b` only. | precise | subordinate norm | cites Theorem 7.1 | Ch7 backward-error theorem | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open; should reuse Chapter 7 theorem when exposed. |
| H17.Eq17_33b.stop_A_backward | p.336, (17.33b) | equivalence | Residual stopping test equivalent to perturbing `A` only. | precise | subordinate norm | cites Theorem 7.1 | Ch7 backward-error theorem | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open; should reuse Chapter 7 theorem when exposed. |
| H17.Eq17_33c.stop_mixed_backward | p.336, (17.33c) | equivalence | Residual stopping test equivalent to perturbing both `A` and `b`. | precise | subordinate norm | cites Theorem 7.1 | Ch7 backward-error theorem | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open; should reuse Chapter 7 theorem when exposed. |
| H17.Tables17_1_17_3_Figure17_1 | pp.322-329 | table/figure/empirical output | Historical dates and MATLAB/SOR/Jacobi plotted or tabulated runs. | empirical/historical | machine-specific | not applicable | MATLAB details, rounding path, random start | SKIP | SKIP-EMPIRICAL | Not encoded in core; mathematical method surfaces remain inventoried above. |
| H17.Problem17_1 | p.337 | problem | benchmark-reserved; statement not transcribed | precise | benchmark | not applicable | none | BENCHMARK_CANDIDATE | BENCHMARK-RESERVED | not encoded. |
| H17.AppA17_1 | Appendix A split ledger | appendix solution | benchmark-reserved; statement not transcribed | precise | benchmark | not applicable | none | BENCHMARK_CANDIDATE | BENCHMARK-RESERVED | not encoded. |

## Reused from Repository or Mathlib

| Source concept/result | Existing declaration | File/module |
|---|---|---|
| Function-shaped real matrix multiplication and powers | `matMul`, `matMulVec`, `matPow`, `matSub_id`, `idMatrix` | `LeanFpAnalysis.FP.Analysis.MatrixAlgebra` |
| Infinity norms and monotone bounds | `infNorm`, `infNormVec`, `infNorm_matMul_le`, `infNorm_matPow_le`, `row_sum_le_infNorm`, `abs_le_infNormVec` | `LeanFpAnalysis.FP.Analysis.MatrixAlgebra` |
| Matrix inverse certificates | `IsLeftInverse`, `IsRightInverse` | `LeanFpAnalysis.FP.Analysis.MatrixAlgebra` |
| Finite sums and real algebra | `Finset` big operators, `linarith`, `ring`, `field_simp` | Mathlib |

## New Dependencies

| Declaration | Why needed | Used by | Feasibility status |
|---|---|---|---|
| `SourceComputedIteration` | Records Higham's actual sign convention in (17.1). | Chapter 17 report and future source-facing recurrence wrappers. | implemented |
| `computedIteration_of_sourceComputedIteration` | Keeps existing legacy proofs reusable without changing all downstream theorem statements. | `one_step_error_source`; future source-sign wrappers. | implemented |
| `one_step_error_source` | Provides a source-sign one-step recurrence directly aligned with (17.1). | Future finite-sum proof of (17.5). | implemented dependency |
| `stationary_solution_fixed_point` | Records the exact-solution affine fixed-point step behind (17.4). | `stationary_solution_finite_sum` and future error recurrence (17.5). | implemented dependency |
| `affine_fixed_point_unroll` | Generic finite unrolling lemma for fixed points of `x = Gx + c`. | `stationary_solution_finite_sum`; future computed/source recurrences may reuse the pattern. | implemented dependency |
| `stationary_solution_finite_sum` | Closes the exact finite-sum identity in (17.4) from `Ax=b` and the splitting certificate. | Future finite-sum error recurrence (17.5). | implemented |
| `matMulVec_finset_sum_right` | Distributes matrix-vector multiplication over finite sums in the vector argument. | `affine_recurrence_unroll`. | implemented dependency |
| `affine_recurrence_unroll` | Generic finite unrolling lemma for affine recurrences with a time-varying source term. | `sourceComputedIteration_finite_sum`, `sourceComputedIteration_error_finite_sum`, `residual_finite_sum`. | implemented dependency |
| `sourceComputedIteration_step_affine` | Applies the left inverse of `M` to Higham's source-sign computed iteration. | `sourceComputedIteration_finite_sum`. | implemented dependency |
| `sourceComputedIteration_finite_sum` | Closes the computed finite-sum identity in (17.3) from the source-sign iteration model. | Future finite-sum error recurrence (17.5). | implemented |
| `sourceComputedIteration_error_finite_sum` | Closes the finite-sum error recurrence in (17.5) by unrolling `one_step_error_source`. | Componentwise finite-sum bounds and future infinite-sum forward-error wrappers. | implemented |
| `residual_finite_sum` | Closes the finite-sum residual recurrence in (17.18) by unrolling `one_step_residual`. | Sigma-form residual bound (17.19) and diagonalizable sigma bound (17.20). | implemented |
| `normwise_residual_sigma_finite_bound` | Converts the closed residual recurrence into the finite sigma-form normwise residual estimate. | Diagonalizable sigma bound (17.20) and future named sigma wrappers. | implemented |

## Open Selected-Scope Items

| Source location | Exact claim | Current Lean status | Missing foundation | Next theorem |
|---|---|---|---|---|
| (17.7), (17.9) | Supremum iterate-growth constants `gamma_x` and `theta_x`. | represented only by explicit hypotheses | bounded/supremum API and zero-component policy | Define finite-prefix or extended-real supremum surfaces, or keep theorem statements hypothesis-based. |
| (17.8), (17.11)-(17.13), (17.15)-(17.16) | Literal infinite-sum normwise/componentwise forward bounds and corollaries. | q-bound/certificate finite forms proved | convergence of matrix-power absolute/norm series; literal `c(A)` minimum/infimum | Add infinite-series/c(A) surface or prove selected finite-horizon equivalents clearly. |
| (17.20) | Diagonalizable sigma bound. | finite-sum residual recurrence, finite sigma-form bound, and q-bound residual theorem proved | diagonalizable/eigenvalue API | Isolate the diagonalizable sigma bound on top of `normwise_residual_sigma_finite_bound`. |
| (17.21)-(17.32) | Singular-system semiconvergence, Drazin inverse, and range/null forward-error bounds. | unstarted | Drazin inverse, semiconvergent matrix powers, index-one decomposition | Create a foundation feasibility table before proof work; likely depends on Ch18/Jordan infrastructure. |
| (17.33a)-(17.33c) | Stopping-test equivalences. | unstarted in Ch17 | reusable Chapter 7 normwise backward-error theorem exposed in compatible norm API | Add thin wrappers over existing Ch7 theorem if available; otherwise keep open. |

## Empirical and Skipped Items

| Source location | Printed claim/output | Missing machine details | Precise subclaim/replacement theorem | Status |
|---|---|---|---|---|
| Table 17.1 | Publication dates and method names. | historical table, no theorem target | stationary-method definitions are inventoried separately | SKIP-HISTORICAL/EDITORIAL |
| Figure 17.1 and SOR opening example | MATLAB SOR trajectory and plotted errors. | MATLAB version, BLAS/LAPACK behavior, exact random/rounded path, plotting data | Stationary iteration, SOR splitting, and forward/residual bounds are formalized as abstract surfaces | SKIP-EMPIRICAL |
| Tables 17.2 and 17.3 | Jacobi experiment outputs. | random start, MATLAB/version/rounding details, termination path | `jacobi_splitting_abs` records the exact Jacobi splitting identity used by the analysis | SKIP-EMPIRICAL |
| Section 17.6 | Notes, implementation sources, and literature review. | bibliographic/software discussion | no selected theorem beyond already inventoried stopping-test comments | SKIP-LITERATURE-REVIEW |

## Hidden-Hypothesis and Weak-Component Summary

- The legacy `ComputedIteration` sign convention is intentionally not presented as identical to source equation (17.1). The new `SourceComputedIteration` wrapper records the source sign and bridges by negating the local error term.
- `sourceComputedIteration_finite_sum` is exact algebra from the source-sign recurrence plus an explicit left-inverse certificate for `M`; it does not assume convergence, a floating-point model, the local-error bound (17.2), or the target error recurrence (17.5).
- `stationary_solution_finite_sum` is exact algebra: its final theorem assumptions are the splitting certificate and `Ax=b`; it does not assume convergence, a floating-point model, or the target finite-sum conclusion.
- `sourceComputedIteration_error_finite_sum` is exact algebra from `one_step_error_source`; it assumes the source-sign iteration model, splitting certificate, and exact solution equation, but does not assume convergence, an infinite series, or any forward-error bound.
- `residual_finite_sum` is exact algebra from `one_step_residual`; it assumes the splitting certificate, exact solution equation, and legacy computed-iteration sign convention, but does not assume convergence, a local-error bound, or any residual norm estimate.
- `normwise_residual_sigma_finite_bound` is a finite sigma-form normwise wrapper over `residual_finite_sum`; it does not introduce a named scalar sigma definition or a diagonalizable eigenvalue estimate.
- Current q-bound forward/residual theorems are stronger-assumption corollaries of the source's infinite-sum style, not closures of the literal (17.8) or (17.11) statements.
- `PartialSumBound` is a finite/certificate surface; it does not prove existence of the literal minimum in (17.12).
- Singular-system claims are all open until a Drazin/semiconvergence foundation is designed and verified.

## Verification

- `lake env lean LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean`: passed after correcting the source labels and adding the source-sign equation (17.1) wrapper.
- `lake build LeanFpAnalysis.FP.Algorithms.StationaryIteration`: passed after the Chapter 17 source-label and wrapper update.
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean docs/source_coverage/higham_ch17.md`: no matches.
- `#print axioms` for `computedIteration_of_sourceComputedIteration` and `one_step_error_source`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env lean LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean`: passed after adding `stationary_solution_fixed_point`.
- `lake build LeanFpAnalysis.FP.Algorithms.StationaryIteration`: passed after adding `stationary_solution_fixed_point`.
- `#print axioms` for `stationary_solution_fixed_point`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean`: no matches after adding `stationary_solution_fixed_point`.
- `lake env lean LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean`: passed after adding `affine_fixed_point_unroll` and `stationary_solution_finite_sum`.
- `lake build LeanFpAnalysis.FP.Algorithms.StationaryIteration`: passed after adding `stationary_solution_finite_sum` and again after the latest `origin/main` merge.
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean`: no matches after adding `stationary_solution_finite_sum`.
- `git diff --check -- LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean`: passed after adding `stationary_solution_finite_sum`, with only the usual CRLF normalization warning before the commit.
- `#print axioms` for `affine_fixed_point_unroll` and `stationary_solution_finite_sum`: only `propext`, `Classical.choice`, and `Quot.sound`.
- Post-merge broad check note: `lake build LeanFpAnalysis.FP.Algorithms.StationaryIteration LeanFpAnalysis.FP.Algorithms.HighamChapter9` exceeded the local timeout while compiling the incoming Chapter 9 side; the lingering Lean/lake processes were stopped. The standalone Chapter 17 file and module checks above passed after the merge.
- `lake env lean LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean`: passed after adding the source-sign computed finite-sum recurrence for (17.3).
- `lake build LeanFpAnalysis.FP.Algorithms.StationaryIteration`: passed after adding `sourceComputedIteration_finite_sum`.
- Merge rebuild after synchronizing with `origin/main`: `lake build LeanFpAnalysis.FP.Algorithms.StationaryIteration LeanFpAnalysis.FP.Algorithms.LeastSquares.LSPerturbation` passed; the second target covered the incoming Chapter 20 merge.
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean`: no matches after adding `sourceComputedIteration_finite_sum`.
- `git diff --check -- LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean`: passed after adding `sourceComputedIteration_finite_sum`, with only the usual CRLF normalization warning before the commit.
- `#print axioms` for `matMulVec_finset_sum_right`, `affine_recurrence_unroll`, `sourceComputedIteration_step_affine`, and `sourceComputedIteration_finite_sum`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env lean LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean`: passed after adding `sourceComputedIteration_error_finite_sum`.
- `lake build LeanFpAnalysis.FP.Algorithms.StationaryIteration`: passed after adding `sourceComputedIteration_error_finite_sum`.
- `#print axioms` for `sourceComputedIteration_error_finite_sum`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env lean LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean`: passed after adding `residual_finite_sum`.
- `lake build LeanFpAnalysis.FP.Algorithms.StationaryIteration`: passed after adding `residual_finite_sum` and again after synchronizing with the latest `origin/main`.
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean`: no matches after adding `residual_finite_sum`.
- `git diff --check -- LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean`: passed after adding `residual_finite_sum`, with only the usual CRLF normalization warning before the commit.
- `#print axioms` for `residual_finite_sum`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env lean LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean`: passed after adding `normwise_residual_sigma_finite_bound`.
- `lake build LeanFpAnalysis.FP.Algorithms.StationaryIteration`: passed after adding `normwise_residual_sigma_finite_bound` and again after the latest `origin/main` merge.
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean`: no matches after adding `normwise_residual_sigma_finite_bound`.
- `git diff --check -- LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean`: passed after adding `normwise_residual_sigma_finite_bound`, with only the usual CRLF normalization warning before the commit.
- `#print axioms` for `normwise_residual_sigma_finite_bound`: only `propext`, `Classical.choice`, and `Quot.sound`.
- Final merge validation for the same milestone: `lake build LeanFpAnalysis.FP.Algorithms.StationaryIteration LeanFpAnalysis.FP.Algorithms.HighamChapter9 LeanFpAnalysis.FP.Algorithms.LeastSquares.LSPerturbation LeanFpAnalysis.FP.Algorithms.LeastSquares.LSQRSolve` passed at synchronized commit `32fb112b`; `lake env lean examples/LibraryLookup.lean` also passed.
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean LeanFpAnalysis/FP/Algorithms/LeastSquares/LSPerturbation.lean LeanFpAnalysis/FP/Algorithms/LeastSquares/LSQRSolve.lean examples/LibraryLookup.lean`: one inspected false-positive prose occurrence of `admit` in an incoming least-squares docstring; no unfinished proof or unsafe placeholder found.
- `git diff --check` over the final merge range passed for the incoming Chapter 9, least-squares, lookup, and Chapter 20 documentation files.

## Git and Local-Only Notes

- `chapter_splitting/` and `References/` are local-only context and must not be staged or pushed.
- Latest synchronized Chapter 17 proof milestone: `normwise_residual_sigma_finite_bound`, pushed to both `origin/main` and `origin/codex/split3b-ch19-main-sync`.
- Remaining local untracked file at this point: `.codex/config.toml`.
