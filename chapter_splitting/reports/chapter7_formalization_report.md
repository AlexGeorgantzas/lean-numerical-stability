# Chapter 7 Formalization Report

Date: 2026-06-19.
Source: `References/1.9780898718027.ch7.pdf`.
Appendix source read: `References/1.9780898718027.appa.pdf`.
Split contract: Split 2, Chapter 7.

## Summary

The library contains substantial Chapter 7 perturbation theory in
`PerturbationTheory.lean` and source-facing Chapter 7 wrappers in
`LeanFpAnalysis.FP.Analysis.HighamChapter7`.

The first proof-completion update added Problem 7.7's Split 2-local comparison
theorems for both the componentwise Oettli-Prager surface and the infinity-norm
Rigal-Gaches surface:

- `problem7_7_componentwise_abs_rhs_to_zero_rhs_residual_bound`
- `problem7_7_componentwise_zero_rhs_feasible_of_abs_rhs_feasible`
- `problem7_7_normwise_inf_residual_bound`
- `problem7_7_normwise_zero_rhs_feasible_of_abs_rhs_feasible`

The local-infrastructure update added the two remaining Split 2-local items
identified after excluding direct/indirect Split 1 dependencies:

- Problem 7.1 local Neumann and exact resolvent infrastructure:
  `ch7Problem71ContractionMatrix`,
  `problem7_1_componentwise_contraction_ineq`,
  `problem7_1_componentwise_neumann_scalar_bound`,
  `ch7NonnegativeResolvent`,
  `problem7_1_resolvent_componentwise_inequality_bound`,
  `ch7NonnegativeResolvent_nonsingInv_of_infNormBound`,
  `problem7_1_componentwise_resolvent_bound`, and
  `problem7_1_componentwise_nonsingInv_resolvent_bound`.
- Problem 7.8 rectangular Frobenius minimization, encoded as lower bound plus
  rank-one attainment:
  `problem7_8_frobenius_characterization_pos`,
  `problem7_8_rankOne_attains_pos`,
  `problem7_8_zero_parameter_attains`, and
  `problem7_8_source_value_eq_augmented_value`.

All Chapter 7 declarations in the Lean module are theorem/definition-level work
with no `sorry`, `admit`, local axioms, orphan typeclass hypotheses, or vacuous
proof-only wrappers. Deferred rows below are not claimed complete.

Classification terms used below:

- `CLOSED`: fully proved for the stated Lean surface.
- `PROVE-NOW-SPLIT2`: selected as local Split 2 work in this pass; all such
  rows are now closed or have an explicit sub-row explaining the remaining
  non-local source generalization.
- `WAIT-SPLIT1`: depends on Split 1-owned norm, rounding, SVD, spectral, or
  condition-distance foundations.
- `DEFER-LATER-SPLIT`: belongs naturally to another split's foundations.
- `DEFER-LATER-CHAPTER`: precise but intentionally after a prerequisite
  Chapter 7 block in this report.
- `SKIP`: empirical, expository, or not a mathematical proof target.

## Verification

Initial Chapter 7 pass verification:

- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean LeanFpAnalysis/FP/Analysis.lean`
- `lake env lean examples/LibraryLookup.lean`
- Full `lake build` passed with 3472 jobs.
- `#print axioms` for the then-new final-facing theorems reported only standard
  Lean foundations: `propext`, `Classical.choice`, and `Quot.sound`.

Proof-completion update verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean > /tmp/higham_library_lookup_ch7_completion.out`
- `rg -n "\b(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
  found no matches.
- `git diff --check -- LeanFpAnalysis/FP/Analysis/HighamChapter7.lean examples/LibraryLookup.lean docs/LIBRARY_LOOKUP.md chapter_splitting/reports/chapter7_formalization_report.md`
- `lake env lean /tmp/ch7_axioms_check.lean` reported only standard Lean
  foundations for the four new Problem 7.7 theorems: `propext`,
  `Classical.choice`, and `Quot.sound`.
- Full `lake build` passed with 3476 jobs. The warnings were pre-existing
  QR/FastMatMul linter warnings outside Chapter 7.

Local-infrastructure update verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean > /tmp/higham_library_lookup_ch7_local.out`
- `rg -n "\b(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
  found no matches.
- `git diff --check -- LeanFpAnalysis/FP/Analysis/HighamChapter7.lean examples/LibraryLookup.lean docs/LIBRARY_LOOKUP.md chapter_splitting/reports/chapter7_formalization_report.md`
- `lake env lean /tmp/ch7_axioms_local_update.lean` reported only standard
  Lean foundations for the new final-facing Problem 7.1 and Problem 7.8
  theorems: `propext`, `Classical.choice`, and `Quot.sound`.
- Full `lake build` passed with 3476 jobs. The warnings were pre-existing
  QR/FastMatMul linter warnings outside Chapter 7.

Exact-resolvent update verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean > /tmp/higham_library_lookup_ch7_exact_resolvent.out`
- `rg -n "\b(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
  found no matches.
- `git diff --check -- LeanFpAnalysis/FP/Analysis/HighamChapter7.lean examples/LibraryLookup.lean docs/LIBRARY_LOOKUP.md chapter_splitting/reports/chapter7_formalization_report.md`
- `lake env lean /tmp/ch7_axioms_exact_resolvent.lean` reported only standard
  Lean foundations for the exact Problem 7.1 resolvent theorems: `propext`,
  `Classical.choice`, and `Quot.sound`.
- Full `lake build` passed with 3476 jobs. The warnings were pre-existing
  QR/FastMatMul linter warnings outside Chapter 7.

## Primary Label Inventory

| Source item | Classification | Lean entry points or decision |
| --- | --- | --- |
| Theorem 7.1, Rigal-Gaches backward error | `CLOSED` for the repository infinity-norm row-sum surface; `WAIT-SPLIT1` for the full arbitrary subordinate-norm source statement | `rigal_gaches_necessary`, `rigal_gaches_sufficient`, `rigal_gaches`; full source statement needs Split 1 generic vector/subordinate norm and dual-norm attainability |
| Theorem 7.2, normwise forward error | `CLOSED` for the componentwise/infinity-norm specialization; `WAIT-SPLIT1` for arbitrary subordinate norms | `normwise_perturbation_bound`, `normwise_forward_error_exact`, `normwise_forward_error_exact_relative_infNorm` |
| Theorem 7.3, Oettli-Prager | `CLOSED` | `oettli_prager_necessary`, `oettli_prager_sufficient`, `oettli_prager` |
| Theorem 7.4, componentwise forward error | `CLOSED` for the infinity-norm relative version; `WAIT-SPLIT1` for arbitrary absolute norms | `componentwise_forward_error`, `componentwise_forward_error_exact`, `componentwise_forward_error_exact_relative_infNorm`, `ch7CondEFAtSolutionInf` |
| Theorem 7.5, van der Sluis diagonal scaling | `WAIT-SPLIT1` | Needs rectangular p-norm, pseudoinverse, rank, and minimization foundations |
| Corollary 7.6, SPD diagonal scaling | `WAIT-SPLIT1` | Depends on Theorem 7.5 plus SPD/2-norm scaling surface |
| Theorem 7.7, Stewart-Sun Frobenius scaling | `WAIT-SPLIT1` | Requires diagonal minimization over nonsingular diagonal matrices and Frobenius/inverse column infrastructure |
| Theorem 7.8, Bauer two-sided scaling | `WAIT-SPLIT1` | Requires Perron-Frobenius and spectral-radius machinery |
| Lemma 7.9, practical error bound | `CLOSED` for the infinity-norm practical bound and equality case | `lemma7_9_componentwise_bound`, `lemma7_9_relative_infNorm_bound`, `lemma7_9_exact_for_residual_multiple` |

## Numbered Equation Ledger

| Equation | Classification | Lean entry points or decision |
| --- | --- | --- |
| (7.1) | `CLOSED` for row-sum infinity specialization; `WAIT-SPLIT1` for arbitrary norm | `rigal_gaches` |
| (7.2) | `CLOSED` for row-sum infinity specialization; `WAIT-SPLIT1` for arbitrary norm | `rigal_gaches` |
| (7.3) | `CLOSED` for row-sum infinity specialization; `WAIT-SPLIT1` for arbitrary norming-vector form | `rigal_gaches_sufficient` |
| (7.4) | `CLOSED` for infinity/componentwise specialization; `WAIT-SPLIT1` for arbitrary subordinate norm | `normwise_forward_error_exact`, `normwise_forward_error_exact_relative_infNorm` |
| (7.5) | `WAIT-SPLIT1` | Generic normwise condition number awaits arbitrary subordinate-norm abstraction |
| (7.6) | `SKIP` | MATLAB/numerical illustration |
| (7.7) | `CLOSED` | `oettli_prager` feasibility surface |
| (7.8) | `CLOSED` | `oettli_prager` |
| (7.9) | `CLOSED` | `oettli_prager_sufficient` construction |
| (7.10) | `CLOSED` for infinity-norm relative version; `WAIT-SPLIT1` for full absolute-norm statement | `componentwise_forward_error_exact_relative_infNorm` |
| (7.11) | `CLOSED` for infinity norm | `ch7CondEFAtSolutionInf` |
| (7.12) | `WAIT-SPLIT1` | Worst-case maximization over `x` depends on generic norm/compactness surface |
| (7.13) | `CLOSED` for infinity norm | `ch7SkeelCondAtSolutionInf` |
| (7.14) | `CLOSED` for infinity norm | `condSkeel`, `ch7SkeelCondAtOnes_eq_condSkeel`, `condSkeel_le_kappaInf` |
| (7.15) | `WAIT-SPLIT1` | Diagonal row scaling minimization |
| (7.16) | `WAIT-SPLIT1` | Diagonal row scaling inequalities |
| (7.17) | `DEFER-LATER-CHAPTER` | Kahan symbolic example should follow the scaling block |
| (7.18) | `WAIT-SPLIT1` | Depends on Theorem 7.5 infrastructure |
| (7.19) | `WAIT-SPLIT1` | Depends on Theorem 7.5 infrastructure |
| (7.20) | `WAIT-SPLIT1` | Depends on Theorem 7.5 infrastructure |
| (7.21) | `WAIT-SPLIT1` | Depends on Theorem 7.5 infrastructure |
| (7.22) | `WAIT-SPLIT1` | Depends on Theorem 7.5 infrastructure |
| (7.23) | `WAIT-SPLIT1` | Depends on Corollary 7.6 infrastructure |
| (7.24) | `WAIT-SPLIT1` | Depends on Perron-Frobenius/Bauer scaling infrastructure |
| (7.25) | `WAIT-SPLIT1` | Inverse componentwise condition-number inequality needs inverse/spectral surface |
| (7.26) | `WAIT-SPLIT1` | Distance-to-singularity result depends on Chapter 6/Split 1 condition-distance foundations |
| (7.27) | `CLOSED` for repository backward-error surfaces | `rigal_gaches`, `oettli_prager` |
| (7.28) | `CLOSED` for infinity norm | `ch7ForwardBoundEF`, `ch7CondEFAtSolutionInf` |
| (7.29) | `CLOSED` for infinity norm | `lemma7_9_relative_infNorm_bound` |
| (7.30) | `WAIT-SPLIT1` | Requires Chapter 3 row-wise computed-residual rounding model |
| (7.31) | `WAIT-SPLIT1` | Depends on (7.30) |
| (7.32) | `DEFER-LATER-CHAPTER` | Calculus perturbation estimate should follow the generic norm/asymptotic interface |
| (7.33) | `CLOSED` | `IsStochasticMatrix`, `stochasticMatrix_mul_ones` |

## Problem Inventory

The Split 2 contract ledger lists Problems 7.1-7.6 and 7.10-7.14. The skill
policy also requires reading and classifying the remaining Chapter 7 problems
and the Appendix A solutions; therefore Problems 7.7-7.9 and 7.15 are listed
explicitly below.

| Problem | Classification | Lean entry points or decision |
| --- | --- | --- |
| 7.1 | `CLOSED` for the scalar Neumann contraction form and the exact matrix-valued resolvent form under the local row-sum contraction hypothesis | `ch7Problem71ContractionMatrix`, `problem7_1_componentwise_contraction_ineq`, `problem7_1_componentwise_neumann_scalar_bound`, `ch7NonnegativeResolvent`, `problem7_1_resolvent_componentwise_inequality_bound`, `ch7NonnegativeResolvent_nonsingInv_of_infNormBound`, `problem7_1_componentwise_resolvent_bound`, `problem7_1_componentwise_nonsingInv_resolvent_bound` |
| 7.2 | `CLOSED` for infinity norm; `WAIT-SPLIT1` for arbitrary subordinate norms | `problem7_2_infNorm_residual_lower`, `problem7_2_infNorm_residual_upper`, `problem7_2_infNorm_scaled_lower`, `problem7_2_infNorm_scaled_upper` |
| 7.3 | `WAIT-SPLIT1` | Depends on diagonal row scaling minimization |
| 7.4 | `WAIT-SPLIT1` | Depends on SPD scaling and condition-number comparison foundations |
| 7.5 | `WAIT-SPLIT1` | Depends on SVD/projection/pseudoinverse foundations |
| 7.6 | `WAIT-SPLIT1` | Depends on row-wise/columnwise condition-number infrastructure and vector 1-norm bridges |
| 7.7 | `PROVE-NOW-SPLIT2` completed; full arbitrary-norm eta generalization remains `WAIT-SPLIT1` | `problem7_7_componentwise_abs_rhs_to_zero_rhs_residual_bound`, `problem7_7_componentwise_zero_rhs_feasible_of_abs_rhs_feasible`, `problem7_7_normwise_inf_residual_bound`, `problem7_7_normwise_zero_rhs_feasible_of_abs_rhs_feasible` |
| 7.8 | `CLOSED` | `ch7Problem78Feasible`, `ch7Problem78AugMatrix`, `ch7Problem78AugVector`, `problem7_8_frobenius_lower_bound_pos`, `problem7_8_rankOne_attains_pos`, `problem7_8_frobenius_characterization_pos`, `problem7_8_zero_parameter_attains`, `problem7_8_source_value_eq_augmented_value` |
| 7.9 | `WAIT-SPLIT1` | Needs generic norm/dual norm and first-order asymptotic infrastructure for `O(epsilon^2)` condition numbers |
| 7.10 | `WAIT-SPLIT1` | Depends on Perron-Frobenius/spectral-radius infrastructure |
| 7.11 | `WAIT-SPLIT1` | Inverse componentwise condition-number formula not yet encoded |
| 7.12 | `DEFER-LATER-SPLIT` | Symmetry-preserving backward error requires QR/Householder plus SPD construction integration |
| 7.13 | `WAIT-SPLIT1` | Sparse residual rounding bound depends on row nonzero-count gamma model |
| 7.14 | `DEFER-LATER-SPLIT` | Probabilistic expected condition-number result needs probability/distribution infrastructure |
| 7.15 | `WAIT-SPLIT1` | Horn-Johnson spectral/Hadamard scaling result depends on spectral-radius/Bauer foundations |

## Proof Integrity

- The newly added Problem 7.1 theorems prove the local contraction inequality,
  scalar Neumann consequence, and exact nonnegative resolvent/nonsingular-
  inverse entrywise bound from Theorem 7.4 plus the existing nonnegative
  infinity-norm contraction infrastructure.
- The newly added Problem 7.8 theorems prove the augmented rectangular
  Frobenius lower bound and construct the rank-one attaining perturbation,
  including the `theta = 0` degenerate case.
- The Problem 7.7 theorems are genuine Lean proofs over the existing
  Oettli-Prager and Rigal-Gaches equivalences; they do not introduce theorem-
  equivalent assumptions or wrapper-only placeholders.
- No local placeholders were introduced for `WAIT-SPLIT1`, `DEFER-LATER-SPLIT`,
  `DEFER-LATER-CHAPTER`, or `SKIP` rows.
- The lookup files name every source-facing Chapter 7 declaration:
  `docs/LIBRARY_LOOKUP.md` and `examples/LibraryLookup.lean`.

## Blocking Foundations

The remaining Chapter 7 rows are blocked by missing or not-yet-integrated local
foundations rather than by Lean errors in the Chapter 7 module:

- Generic vector norms and arbitrary subordinate matrix norms for exact source
  statements of Theorems 7.1, 7.2, Theorem 7.4, Problem 7.2, Problem 7.7's
  arbitrary-norm eta form, and equation (7.5).
- Absolute-norm interface for the full source statement of Theorem 7.4.
- Pseudoinverse, rank, SVD projection, and diagonal scaling minimization for
  Theorem 7.5, Corollary 7.6, and Problem 7.5.
- Perron-Frobenius/spectral-radius theory for Theorem 7.8, Problem 7.10, and
  Problem 7.15.
- Computed-residual rounding model with row nonzero counts for (7.30), (7.31),
  and Problem 7.13.
- Probability/distribution infrastructure for Problem 7.14.
