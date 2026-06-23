# Higham Chapter 3 Formalization Report

## Source and scope

- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM).
- Chapter: Chapter 3, "Basics".
- Printed pages: 61-78 in the chapter PDF; Appendix A solution rows on pp. 536-538.
- Source file: `References/1.9780898718027.ch3.pdf`.
- Mode: core.
- Parallel split: 1.
- Planning documents consulted: `HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md`, Split 1 of `split_primary_contracts.md`, and `chapter_index.md`.
- Selected-scope gate: PASS after the Chapter 3 patches and validation commands recorded below.

## Closure added in this pass

| Source label | Lean declaration | File | Theorem surface | Notes |
|---|---|---|---|---|
| Lemma 3.7 | `matSeqProd_mixed_normwise_perturbation_bound` | `LeanFpAnalysis/FP/Analysis/MatrixAlgebra.lean` | Mixed-norm finite-product perturbation induction with one norm `NF` for the perturbation/error and one norm `NS` for the unperturbed factors. | This is the repository-facing core of the Frobenius/operator-2 source lemma. The theorem exposes the norm laws used by the book instead of hiding them. |
| Source labels | Comment/docstring label corrections | `DotProduct.lean`, `Rounding.lean`, `MatMul.lean`, `MatSeqProduct.lean`, `SquareDifference.lean`, `ComplexBackwardError.lean`, `ComplexArithmetic.lean`, `MatVec.lean`, `RankOneUpdate.lean`, `MatrixAlgebra.lean` | Corrected off-by-one Chapter 3 equation/problem/lemma references. | These were documentation/source-traceability fixes; theorem statements did not weaken. |
| Repository navigation | README and lookup checks | `README.md`, `examples/LibraryLookup.lean` | README now names `matSeqProd_mixed_normwise_perturbation_bound`; lookup checks include it. | Chapter 3 no longer silently folds Lemma 3.7 into Lemma 3.6. |

## Primary labels

| Source label | Decision | Lean artifact/status |
|---|---|---|
| Lemma 3.1 | FORMALIZE_CORE | Closed by `prod_error_bound` and `prod_signed_error_bound` in `Rounding.lean`. |
| Algorithm 3.2 | FORMALIZE_CORE | Closed by `runningError_bound_from_local_errors` and `fl_runningDotProduct_error_bound_from_inverse_models`. |
| Lemma 3.3 | FORMALIZE_CORE | Closed by `gamma_mul`, `gamma_inv`, `gamma_div`, `gamma_div_le_branch`, `gamma_div_gt_branch`, `gamma_sum_le`, `gamma_add_u_le`, `gamma_nsmul_le`, `gamma_prod_le`, and the relative-error-counter lemmas. |
| Lemma 3.4 | FORMALIZE_CORE | Closed by `prod_one_add_delta_eq_one_add_eta_bound_101` and `prod_one_add_delta_eq_one_add_eta_bound_101_le`. |
| Lemma 3.5 | FORMALIZE_CORE | Closed by `complexRelErrorModel`, `fl_complexAdd_rel_error_model`, `fl_complexSub_rel_error_model`, `fl_complexMul_rel_error_model`, `fl_complexDiv_rel_error_model`, and Smith-division variants. |
| Lemma 3.6 | FORMALIZE_CORE | Closed by `matSeqProd_normwise_perturbation_bound`. |
| Lemma 3.7 | FORMALIZE_CORE | Closed by `matSeqProd_mixed_normwise_perturbation_bound`, the mixed-norm induction core for the Frobenius/operator-2 variant. |
| Lemma 3.8 | FORMALIZE_CORE | Closed by `matSeqProd_componentwise_perturbation_bound`. |
| Lemma 3.9 | FORMALIZE_CORE | Closed by `fl_rankOneUpdate_componentwise_error_bound` and `fl_rankOneUpdate_error_bound_vecNorm2`. |

## Numbered equations

| Equation | Decision | Lean artifact/status |
|---|---|---|
| (3.1) | FORMALIZE_CORE | `dotProduct_factor_expansion_succ` covers the two-term expansion pattern. |
| (3.2) | FORMALIZE_CORE | `dotProduct_factor_expansion_succ` and `dotProduct_factor_expansion_sum_succ` package the left-to-right dot-product local-factor expansion. |
| (3.3) | FORMALIZE_CORE | `dotProduct_backward_error` gives the backward-error expansion with per-term `gamma` witnesses. |
| (3.4) | FORMALIZE_CORE | `dotProduct_backward_stable_x`, `dotProduct_backward_stable_y`, and `dotProduct_isRelBackwardStable`. |
| (3.5) | FORMALIZE_CORE | `dotProduct_error_bound` gives the `gamma_n |x|^T |y|` forward bound. |
| (3.6) | FORMALIZE_CORE | `outerProduct_error_bound`, `outerProduct_error_decomposition`, and the non-global-backward counterexample surface. |
| (3.7) | FORMALIZE_CORE | Closed by exact finite `gamma` and small-`nu` bounds, especially `dotProduct_error_bound_101_succ`. The source's `O(u^2)` display is recorded via the stronger finite theorem. |
| (3.8) | SKIP | SKIP-TERMINOLOGY. This is notation `gamma_tilde_k = c k u / (1 - c k u)` with unspecified small integer `c`; exact `gamma` and small-`nu` theorem surfaces are used instead. |
| (3.9) | FORMALIZE_CORE | `dotProduct_error_bound_101_succ`. |
| (3.10) | FORMALIZE_CORE | `relErrorCounter`, `relErrorCounter_abs_sub_one_le_gamma`, `relErrorCounter_mul`, `relErrorCounter_inv`, `relErrorCounter_div`. |
| (3.11) | FORMALIZE_CORE | `matVec_backward_error`; `fl_matVecSaxpy_eq_sdot` records the sdot/saxpy equivalence used by the source discussion. |
| (3.12) | FORMALIZE_CORE | `matVec_error_bound`, `matVec_error_bound_infNorm`, `matVec_error_bound_oneNorm`, `matVec_error_bound_infNormRect`, `matVec_error_bound_oneNormRect`. |
| (3.13) | FORMALIZE_CORE | `matMul_error_bound` and its normwise majorants, plus `matMul_forward_bound_sharp_A` and `matMul_forward_bound_sharp_B`. |
| (3.14a) | FORMALIZE_CORE | `fl_complexAdd_rel_error_model` and `fl_complexSub_rel_error_model`. |
| (3.14b) | FORMALIZE_CORE | `fl_complexMul_rel_error_model`. |
| (3.14c) | FORMALIZE_CORE | `fl_complexDiv_rel_error_model`; Smith-form variants record the later overflow-avoiding branch analysis without treating it as a Chapter 3 empirical obligation. |
| (3.14) | FORMALIZE_CORE | The combined complex arithmetic model is closed by the Lemma 3.5 theorem family. |

## Problem ledger

| Problem | Decision | Reason code | Lean artifact/status |
|---|---|---|---|
| 3.1 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Proof of Lemma 3.1 is closed by `prod_error_bound` and `prod_signed_error_bound`. |
| 3.2 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `prod_one_add_delta_eq_one_add_phi_bound_problem32` and related product bounds. |
| 3.3 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `continuedFraction_step_error_le` and `continuedFraction_running_error_bound`. |
| 3.4 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Proof of Lemma 3.3 is closed by the `gamma_*` and `relErrorCounter_*` theorem family. |
| 3.5 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `matMul_backward_error_common_A_of_inverse` and `matMul_backward_error_common_B_of_inverse`. |
| 3.6 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `matMulRelativeBackwardFeasible_residual_entry_le`, `matMulRelativeBackwardFeasible_sqrt_lower_bound_entry`, `matMulWeightedBackwardFeasible_residual_entry_le`, `matMulWeightedBackwardFeasible_sqrt_lower_bound_entry`, and `matMulMixedBackwardForwardFeasible`. |
| 3.7 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `complexDotProduct_backward_stable_y`, `complexDotProduct_backward_stable_x`, and `complexMatVec_backward_error`. |
| 3.8 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `squareDiff_factor_identity`, `fl_squareDiff_direct_error_bound`, `fl_squareDiff_factored_rel_error`, and `fl_squareDiff_factored_error_bound`. |
| 3.9 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Proof of Lemma 3.6 is closed by `matSeqProd_normwise_perturbation_bound`. |
| 3.10 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by the finite-budget theorem `matPrefixProd_error_bound_from_local_errors` and uniform corollary `matPrefixProd_error_bound_uniform`; the source's `O(u^2)` wording is represented by exact finite budgets. |
| 3.11 | SKIP + REUSE_EXISTING | SKIP-EMPIRICAL | The printed Pentium III/MATLAB output is empirical-source-output. The exact recurrence mechanisms and conditional phase-law/display theorems in `KahanAbsolute.lean` close the formalizable mathematical phenomenon. |
| 3.12 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `quadratureRule`, `fl_quadrature`, and `fl_quadrature_error_bound_of_function_value_rel_error`. |

## Empirical source outputs

| Source location | Printed claim/output | Missing machine details | Precise subclaim/replacement theorem | Status |
|---|---|---|---|---|
| Problem 3.11 | MATLAB output for `absolute(x,50)` on a Pentium III workstation, with vector `x = [.25 .5 .75 1.25 1.5 2]` and printed `z`. | Exact MATLAB version, libm/sqrt semantics, decimal input/output and display rounding, processor rounding state, compiler/runtime behavior, subnormal/exception handling, and whether all intermediate results are forced to IEEE double at every step. | `kahanAbsoluteExactFromSquareSteps_eq_abs`, `kahanAbsoluteProblem311IeeeDouble_initialSquare_exact`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_*`, and conditional display/phase-law theorems explain the machine-independent mechanism. | SKIP-EMPIRICAL for the historical output; formalizable mechanisms closed and visible. |

## Skipped and deferred items

| Source location | Summary | Reason code | Status |
|---|---|---|---|
| Eq. (3.8) | `gamma_tilde_k` shorthand with unspecified small integer `c`. | SKIP-TERMINOLOGY | Not a standalone theorem. Exact `gamma` and small-`nu` bounds are formalized. |
| Figures, prose motivation, historical notes, and literature-review paragraphs | Explanatory or bibliographic material with no precise theorem claim. | SKIP-EDITORIAL / SKIP-LITERATURE-REVIEW | Non-gating. |
| Problem 3.11 historical workstation rows | Observed machine output. | SKIP-EMPIRICAL | Recorded above; not promoted to a Lean theorem without a fully specified machine model. |

## Open selected-scope items

None for Chapter 3 core mode after this pass.

The only non-core exclusions are correctly classified notation-only, editorial, bibliographic, or empirical-source-output rows. The Lemma 3.7 theorem is stated at the repository's abstract mixed-norm interface; it exposes, rather than assumes away, the norm properties needed to instantiate Frobenius/operator-2 variants.

## Hidden-hypothesis and weak-component summary

- Lemma 3.7 is weak because a previous report could overstate the generic consistent-norm Lemma 3.6 as closing the mixed Frobenius/operator-2 statement. The new theorem separates the two norm roles and lists the required mixed multiplication laws explicitly.
- Equation labels (3.8)-(3.14) and Problems 3.8-3.10 were weak because several docstrings had old off-by-one references. The touched comments and README rows now match the PDF.
- Problem 3.11 is weak because it mixes a formalizable recurrence/roundoff mechanism with under-specified historical output. The empirical row is preserved and does not block the selected mathematical gate.
- Problem 3.10 is weak because the source uses `O(u^2)`. The repository closes it by exact finite-budget theorems; no arbitrary asymptotic constant was invented.

## Verification

- Focused Lean checks passed for:
  - `LeanFpAnalysis/FP/Analysis/Rounding.lean`
  - `LeanFpAnalysis/FP/Analysis/MatrixAlgebra.lean`
  - `LeanFpAnalysis/FP/Algorithms/DotProduct.lean`
  - `LeanFpAnalysis/FP/Algorithms/MatSeqProduct.lean`
  - `LeanFpAnalysis/FP/Algorithms/MatMul.lean`
  - `LeanFpAnalysis/FP/Algorithms/MatVec.lean`
  - `LeanFpAnalysis/FP/Analysis/ComplexArithmetic.lean`
  - `LeanFpAnalysis/FP/Algorithms/RankOneUpdate.lean`
  - `LeanFpAnalysis/FP/Algorithms/SquareDifference.lean`
  - `LeanFpAnalysis/FP/Algorithms/ComplexBackwardError.lean`
  - `LeanFpAnalysis/FP/Algorithms/Quadrature.lean`
  - `LeanFpAnalysis/FP/Algorithms/KahanAbsolute.lean`
  - `LeanFpAnalysis/FP/Algorithms/OuterProduct.lean`
- `git diff --check`: PASS.
- Lean-source placeholder scan, `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis Main.lean examples`: PASS with no matches.
- `lake build`: PASS, 3471 jobs. Warnings in QR/FastMatMul are pre-existing baseline linter warnings, not introduced by Chapter 3 edits.
- `lake env lean examples/LibraryLookup.lean`: PASS after rebuilding the changed modules.
- `#print axioms` for `matSeqProd_mixed_normwise_perturbation_bound`, `fl_quadrature_error_bound_of_function_value_rel_error`, `fl_rankOneUpdate_componentwise_error_bound`, and `complexMatVec_backward_error`: only standard Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Documentation

- Inventory/report path: `chapter_splitting/reports/split1_ch03_core_audit.md`.
- No separate proof-source or bottleneck ledger was triggered for Chapter 3 core mode.
- No theorem PDF was generated for this chapter pass.
