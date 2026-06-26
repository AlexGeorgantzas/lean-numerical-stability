# Higham Chapter 10 Formalization Report

## Source and Scope

- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. SIAM e-book chapter PDF, ISBN-derived repository source `1.9780898718027.ch10.pdf`.
- Chapter: 10, Cholesky Factorization.
- Printed pages: 195-212.
- Source files: `References/1.9780898718027.ch10.pdf`; Appendix A source `References/1.9780898718027.appa.pdf`.
- Mode: proof-completion, core selected scope.
- Parallel split: Split 2.
- Planning documents consulted: `HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md`, Split 2 section of `split_primary_contracts.md`, and Chapter 10/AppA rows of `chapter_index.md`.
- Selected-scope gate: FAIL for the full source chapter because full floating-point Cholesky, spectral/norm perturbation, rank-pivoting, and several Appendix rows remain current Split 2 proof/API targets over integrated Split 1 foundation families. The local `PROVE-NOW-SPLIT` rows identified in this pass are closed below.

## Completed Selected Targets

| Source label | Lean declaration | File | Theorem surface | Notes |
| --- | --- | --- | --- | --- |
| Theorem 10.1 | `higham10_1_cholesky_existence`, `higham10_1_cholesky_uniqueness` | `LeanFpAnalysis/FP/Algorithms/HighamChapter10.lean` | Exact SPD Cholesky existence/uniqueness via `CholeskyFactSpec` | Reused genuine exact proof chain from `CholeskySpec`; no unresolved integrated Split 1 blocker. |
| Section 10.1 Cholesky `A = L D L^T` rewrite | `higham10_1_choleskyLDLTLower`, `higham10_1_choleskyLDLTDiagonal`, `higham10_1_cholesky_to_ldlt` | `LeanFpAnalysis/FP/Algorithms/HighamChapter10.lean` | Any exact upper Cholesky certificate induces a unit-lower `L` and diagonal `D` satisfying the existing block-LDLT spec with identity permutation | Newly proved in the Split 2 unifying continuation; no integrated previous-split blocker. |
| Problem 10.1 | `higham10_spd_diag_pos`, `higham10_problem_10_1_two_by_two_minor_pos`, `higham10_problem_10_1_abs_offdiag_lt_sqrt_diag_mul`, `higham10_problem_10_1_abs_entry_le_largest_diag`, `higham10_problem_10_1_maxEntryNorm_eq_largest_diag` | `LeanFpAnalysis/FP/Algorithms/HighamChapter10.lean` | SPD diagonal positivity, strict off-diagonal bound, and max-entry-on-diagonal conclusion | Newly proved in this pass; no integrated previous-split blocker. |
| Problem 10.4 | `spd_schur_complement_isSymPosDef`, `higham10_problem_10_4_first_ge_reduced_submatrix_spd`, `higham10_problem_10_4_first_ge_entry_abs_le_initial_max`, `higham10_problem_10_4_first_ge_maxEntryNorm_le`, `higham10_problem_10_4_unpivotedGEGrowthBounded`, `higham10_problem_10_4_unpivoted_ge_positive_pivots_and_growth` | `Cholesky/CholeskySpec.lean`, `HighamChapter10.lean` | Exact SPD GE Schur step is SPD; every unpivoted GE pivot is positive; nonempty Schur-stage max-entry norms do not increase, giving growth factor at most `1` | Newly proved/exposed in this pass; no integrated previous-split blocker. |
| Theorem 10.9(a) | `higham10_9_psd_cholesky_existence` | `HighamChapter10.lean` | Exact PSD Cholesky existence `A = R^T R` with nonnegative diagonal | Reused genuine exact proof chain from `CholeskyPSD`; no unresolved integrated Split 1 blocker. |
| Problem 10.8 witness | `higham10_problem_10_8_counterexample`, `higham10_problem_10_8_leading_minors_nonnegative`, `higham10_problem_10_8_counterexample_symmetric`, `higham10_problem_10_8_counterexample_not_psd` | `HighamChapter10.lean` | Concrete symmetric `2 x 2` witness with nonnegative leading determinant formulas but not PSD | Newly proved in this pass; the general principal-minor criterion is not closed. |
| Section 10.4 equivalence | `higham10_29_symmetric_skew_decomposition`, `higham10_29_nonsymPosDef_iff_symPartSPD` | `HighamChapter10.lean` | Decomposition into symmetric/skew parts and equivalence with SPD symmetric part | Reused genuine exact proof chain from `CholeskyNonsym`; no unresolved integrated Split 1 blocker. |

## Reused From Repository or Mathlib

| Source concept/result | Existing declaration | File/module |
| --- | --- | --- |
| Exact SPD Cholesky | `cholesky_existence`, `cholesky_uniqueness`, `CholeskyFactSpec` | `LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskySpec` |
| Block LDLT source specification | `BlockLDLTSpec`, `IsBlockDiag` | `LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` |
| Exact PSD Cholesky | `psd_cholesky_existence`, `IsPosSemiDef` | `LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyPSD` |
| Cholesky certificate perturbation | `cholesky_backward_error_perturbation` | `Cholesky.CholeskySpec` |
| Cholesky solve certificate perturbation | `cholesky_solve_backward_error` | `Cholesky.CholeskySolve` |
| Schur-complement SPD proof | `schur_sym`, `schur_pd` exposed through `spd_schur_complement_isSymPosDef` | `Cholesky.CholeskySpec` |
| Max-entry norm | `maxEntryNorm`, `entry_le_maxEntryNorm` | `LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor` |
| Nonsymmetric positive-definite equivalence | `nonsymPosDef_iff_symPartSPD`, `symmetric_skew_decomposition` | `Cholesky.CholeskyNonsym` |

## New Dependencies

| Declaration | Why needed | Used by | Feasibility status |
| --- | --- | --- | --- |
| `higham10_spd_diag_pos` | Public diagonal positivity for arbitrary `Fin n` SPD matrices | Problem 10.1 and max-entry proof | closed-local |
| `higham10_1_choleskyLDLTLower`, `higham10_1_choleskyLDLTDiagonal`, `higham10_1_cholesky_to_ldlt` | Close the same-split deferred Section 10.1 Cholesky-to-LDLT rewrite using the Chapter 11 block-LDLT spec | Section 10.1 additional precise prose row and unified cross-chapter audit | closed-local |
| `higham10_problem_10_1_two_by_two_minor_pos` | Quadratic-discriminant core of Problem 10.1 | Problem 10.1 off-diagonal theorem | closed-local |
| `spd_schur_complement_isSymPosDef` | Public exact first-stage Schur complement SPD lemma | Problem 10.4 first assertion | closed-local |
| `higham10_problem_10_4_first_ge_maxEntryNorm_le` | One-step max-entry nonincrease for an SPD Schur complement | Problem 10.4 growth induction | closed-local |
| `higham10_problem_10_4_unpivoted_ge_positive_pivots_and_growth` | Recursive exact GE invariant for all SPD Schur stages | Problem 10.4 no-pivot/growth claim | closed-local |
| `higham10_problem_10_8_counterexample` | Exact witness for Problem 10.8 | Problem 10.8 witness theorems | closed-local |

## Source Inventory and Decisions

### Primary Labels

| ID | Source item | Classification | Previous-split dependency | Exact blocker or closure | Lean artifact/status |
| --- | --- | --- | --- | --- | --- |
| P10-T10.1 | Theorem 10.1, exact SPD Cholesky | CLOSED | No integrated previous-split blocker | Closed exact proof | `higham10_1_cholesky_existence`, `higham10_1_cholesky_uniqueness` |
| P10-A10.2 | Algorithm 10.2, concrete Cholesky loop and flop count | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait | Split 1 `H02.rounding_model`, `H03.gamma_theta`, sqrt-operation rounding and theta product model; exact loop/cost modeling should not be redefined locally | Certificate predicate `higham10_2_CholeskyBackwardError`; concrete `fl_cholesky` path open |
| P10-T10.3 | Theorem 10.3, computed-factor backward error | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait | Needs Algorithm 10.2 certificate generation from Split 1 rounding/gamma foundations; do not assume the certificate as the source theorem | Certificate consequence `higham10_3_cholesky_backward_error` closed |
| P10-T10.4 | Theorem 10.4, Cholesky solve backward error | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait | Needs concrete factorization certificate plus Split 1 gamma absorption; triangular-solve side is available | Certificate consequence `higham10_4_cholesky_solve_backward_error` closed |
| P10-T10.5 | Theorem 10.5, Demmel `d d^T` bound | PROVE-NOW-SPLIT2 | Yes, indirect integrated Split 1 dependency; not an unresolved wait | Depends on full Theorem 10.3 concrete Cholesky backward-error route and Split 1 norm/gamma foundations | Interface `higham10_5_demmel_bound`; full diagonal source derivation open |
| P10-T10.6 | Theorem 10.6, scaled forward error | PROVE-NOW-SPLIT2 | Yes, indirect integrated Split 1 dependency; not an unresolved wait | Uses van der Sluis/condition-number scaling from Chapter 7, now a current wrapper/API target over integrated `H06.svd` and condition-number tools, plus concrete Cholesky error | Interface `higham10_6_scaled_forward_error`; `higham10_9_vanDerSluisScalingBound` predicate |
| P10-T10.7 | Theorem 10.7, success/failure thresholds | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait | Needs Split 1 `H06.svd`/eigenvalue/interlacing/operator-norm tools and Split 1 rounding/gamma route for concrete stages | Sign consequences `higham10_7_success_condition`, `higham10_7_failure_condition` closed only as interfaces |
| P10-T10.8 | Theorem 10.8, Sun perturbation bounds | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait | Needs operator 2-norm/spectral/condition-number perturbation infrastructure from Split 1 `H06`; source proof is citation-only | Interfaces `higham10_8_sun_normwise_perturbation`, `higham10_8_sun_componentwise_perturbation` |
| P10-T10.9a | Theorem 10.9(a), PSD Cholesky existence | CLOSED | No integrated previous-split blocker | Closed exact proof by local induction | `higham10_9_psd_cholesky_existence` |
| P10-T10.9b | Theorem 10.9(b), rank-r pivoted PSD Cholesky | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait | Needs rank/nullspace/minor/SVD-backed rank display and pivot trace API from Split 1 `H06.svd`/rank foundations; should not be replaced by a local rank API | Full-rank SPD specialization `higham10_9_spd_pivoted_cholesky_full_rank`; rank-r source row open |
| P10-L10.10 | Lemma 10.10, Schur-complement perturbation | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait | Needs Split 1 norm/asymptotic inverse-perturbation infrastructure for the `O(||E||^2)` estimate | Interface `higham10_10_schur_complement_perturbation` |
| P10-L10.11 | Lemma 10.11, no-tie pivot perturbation | PROVE-NOW-SPLIT2 | Yes, indirect integrated Split 1 dependency; not an unresolved wait | Depends on Lemma 10.10's perturbation estimate plus formal pivot sequence/no-tie continuity | No closed theorem |
| P10-L10.12 | Lemma 10.12, `||A11^{-1} A12||` bound | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait | Needs Split 1 `H06` operator 2-norm, square-root, and Schur-complement norm tools | Interface `higham10_12_w_norm_bound_from_cond` |
| P10-L10.13 | Lemma 10.13, complete-pivoting `W` bound and sharp family | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait | Needs Split 1 norm/rank foundations plus complete-pivoting trace; do not reprove a parallel norm API locally | Predicate/interface `higham10_13_completePivotingInequality`, `higham10_13_complete_pivoting_w_bound` |
| P10-T10.14 | Theorem 10.14, PSD Cholesky backward error | PROVE-NOW-SPLIT2 | Yes, direct and indirect integrated Split 1 dependency; not an unresolved wait | Direct: Split 1 gamma/norm/eigenvalue; indirect: Theorems 10.7, Lemma 10.10, rank-r pivoted Cholesky | Interface `higham10_14_psd_cholesky_backward_error` |

### Numbered Equations

| Equation | Classification | Previous-split dependency | Lean artifact/status |
| --- | --- | --- | --- |
| (10.1) | CLOSED | No integrated previous-split blocker | Covered by exact `CholeskyFactSpec` product surface in Theorem 10.1 |
| (10.2) | CLOSED | No integrated previous-split blocker | Covered by exact Cholesky construction; not exported separately |
| (10.3) | CLOSED | No integrated previous-split blocker | Covered by exact Cholesky construction; not exported separately |
| (10.4) | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait: Split 1 `H03.gamma_theta`, `H03.inner_product_bounds` and sqrt rounding | Certificate predicate only |
| (10.5) | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait: Algorithm 10.2 certificate generation from Split 1 rounding/gamma | Certificate consequence `higham10_3_cholesky_backward_error` closed |
| (10.6) | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait: concrete Cholesky plus triangular solve gamma absorption | Certificate consequence `higham10_4_cholesky_solve_backward_error` closed |
| (10.7) | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait: Split 1 `H06.norms`, operator 2-norm and gamma simplification | Existing normwise theorem has different hypotheses; source row open |
| (10.8) | PROVE-NOW-SPLIT2 | Yes, indirect integrated Split 1 dependency; not an unresolved wait through full Theorem 10.3 and norm foundations | Interface `higham10_5_demmel_bound` |
| (10.9) | PROVE-NOW-SPLIT2 | Yes, indirect integrated Split 1 dependency; not an unresolved wait through the Chapter 7 van der Sluis wrapper target over integrated `H06.svd` | Predicate `higham10_9_vanDerSluisScalingBound` |
| (10.10) | PROVE-NOW-SPLIT2 | Yes, indirect integrated Split 1 dependency; not an unresolved wait through (10.9) and full Cholesky error | Interface `higham10_6_scaled_forward_error` |
| (10.11) | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait: Split 1 rank/SVD foundations for rank-r PSD display | Predicate `higham10_9_PivotedCholeskySpec`; SPD full-rank specialization closed |
| (10.12) | CLOSED | No integrated previous-split blocker | Definition `higham10_12_outerProductResidual` |
| (10.13) | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait: Split 1 norm/rank tools plus pivot trace | Predicate `higham10_13_completePivotingInequality` |
| (10.14) | CLOSED | No integrated previous-split blocker | Definition `higham10_14_schurComplement` |
| (10.15) | CLOSED | No integrated previous-split blocker | Definition `higham10_14_schurComplement` |
| (10.16) | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait: Split 1 norm/asymptotic inverse perturbation | Interface `higham10_10_schur_complement_perturbation` |
| (10.17) | PROVE-NOW-SPLIT2 | Yes, indirect integrated Split 1 dependency; not an unresolved wait through Lemma 10.10 and pivot continuity | No closed theorem |
| (10.18) | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait: Split 1 operator norm and block identity matrix norm tools | Source example not encoded |
| (10.19) | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait: Split 1 norm/rank plus complete-pivoting trace | Interface `higham10_13_complete_pivoting_w_bound` |
| (10.20) | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait: Split 1 norm/rank and Kahan-family sharpness machinery | No closed theorem |
| (10.21) | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait: Split 1 eigenvalue/minimum-eigenvalue foundations | Not represented in final theorem surface |
| (10.22) | PROVE-NOW-SPLIT2 | Yes, direct and indirect integrated Split 1 dependency; not an unresolved wait: Split 1 gamma/norm plus Theorem 10.7/Lemma 10.10 | Interface `higham10_14_psd_cholesky_backward_error` |
| (10.23) | PROVE-NOW-SPLIT2 | Yes, indirect integrated Split 1 dependency; not an unresolved wait through full PSD algorithm trace | No separate theorem |
| (10.24) | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait: Split 1 gamma/norm and rank estimates | No separate theorem |
| (10.25) | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait: Split 1 gamma/norm estimates | No separate theorem |
| (10.26) | CLOSED | No integrated previous-split blocker | Predicate `higham10_26_nonpositivePivotCriterion` |
| (10.27) | CLOSED | No integrated previous-split blocker for criterion; reliability proof depends on previous rows | Predicates `higham10_27_residualStopCriterion`, `higham10_27_nonpositiveDiagonalCriterion`; abstract bound wrapper |
| (10.28) | CLOSED for criterion | No integrated previous-split blocker for criterion; condition-number bound uses upstream norm tools | Predicate `higham10_28_relativeDiagonalStopCriterion`; bound not closed |
| (10.29) | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait: Split 1 Frobenius/operator norm and condition-number infrastructure plus LU growth proof | Decomposition/equivalence closed; growth bound interface only |
| (10.30) | CLOSED | No integrated previous-split blocker for the displayed class definition | Definition `higham10_30_complexPositiveDefiniteForm`; cited growth theorem skipped/deferred below |

### Problems and Appendix A

| Problem | Classification | Previous-split dependency | Exact reason/status |
| --- | --- | --- | --- |
| 10.1 | CLOSED | No integrated previous-split blocker | Newly proved off-diagonal bound and max-entry consequence. |
| 10.2 | SKIP | No integrated previous-split blocker | Computational recipe for evaluating `x^T A^{-1} x`; no selected theorem beyond nonnegativity of a square sum. |
| 10.3 | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait: Split 1 `H02.rounding_model`, `H03.gamma_theta` and square-root rounding | Arbitrary-order product/sqrt recurrence not locally available. |
| 10.4(a) | CLOSED | No integrated previous-split blocker | Newly exposed first-stage Schur complement SPD theorem. |
| 10.4(b) | CLOSED | No integrated previous-split blocker | Newly proved recursive exact unpivoted-GE invariant: each SPD Schur stage has positive pivot and nonincreasing max-entry norm. |
| 10.5 | PROVE-NOW-SPLIT2 | Yes, indirect integrated Split 1 dependency; not an unresolved wait through full Theorem 10.5/(10.6) and Split 1 norm/gamma | Max-entry norm target now has Problem 10.1 diagonal max bridge; full backward-error result remains open. |
| 10.6 | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait: Split 1 rank/nullspace/SVD foundations | Nullspace basis proof not closed. |
| 10.7 | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait: Split 1 norm/rank and complete-pivoting trace | Predicate for (10.13) exists; proof open. |
| 10.8 | CLOSED for witness; PROVE-NOW-SPLIT2 for general criterion | Witness: no integrated previous-split blocker. Criterion: direct Split 1 determinant/minor/rank foundations | Concrete counterexample closed; principal-minor iff PSD theorem not closed. |
| 10.9 | PROVE-NOW-SPLIT2 | Yes, indirect integrated Split 1 dependency; not an unresolved wait through Schur-complement/rank infrastructure | Negative-curvature direction needs block/rank/Schur complement APIs. |
| 10.10 | SKIP | No integrated previous-split blocker | Explanatory diagnosis of invalid continuity argument; no independent theorem selected beyond Theorem 10.14 blocker. |
| 10.11 | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait: complex Hermitian positive-definite and Schur-complement foundations | Complex/Hermitian Schur complement theorem not locally available. |
| 10.12 | SKIP | No integrated previous-split blocker | Research problem; no determinate theorem statement. |

### Additional Precise Prose, Algorithms, and Empirical Rows

| Source location | Summary | Classification | Previous-split dependency | Reason/status |
| --- | --- | --- | --- | --- |
| Section 10.1 prose | `A = L D L^T` rewrite of Cholesky | CLOSED | No integrated previous-split blocker | `higham10_1_cholesky_to_ldlt` constructs the unit-lower factor and diagonal factor from any exact Cholesky certificate and proves the existing `BlockLDLTSpec` product with identity permutation. |
| Section 10.1 prose | Solve `Ax=b` via `R^T y=b`, `Rx=y` | CLOSED for certificate solve form | Uses already available triangular solve results | `higham10_4_cholesky_solve_backward_error`. |
| Section 10.1.1 prose | Growth factor for GE is exactly 1 | CLOSED | No integrated previous-split blocker | Closed as the recursive exact SPD Schur-stage max-entry nonincrease theorem `higham10_problem_10_4_unpivoted_ge_positive_pivots_and_growth`. |
| Section 10.3 prose | Complete pivoting equivalent to GE complete pivoting because PSD largest element lies on diagonal | CLOSED for largest-element ingredient; PROVE-NOW-SPLIT2 for pivoting equivalence | Pivoting equivalence has direct or indirect integrated Split 1 dependency through pivot trace | Problem 10.1 closes largest-entry ingredient. |
| Section 10.3.2 prose | LINPACK/xCHDC stopping effectiveness and `||W||` usually small | SKIP | No integrated previous-split blocker | Empirical/practical-experience statements; no formal theorem selected. |
| Section 10.4 prose | Matrices with positive definite symmetric part have nonsingular leading principal submatrices and positive pivots | PROVE-NOW-SPLIT2 | Yes, direct integrated Split 1 dependency; not an unresolved wait through determinant/minor and exact LU pivot foundations | Equivalence with SPD symmetric part is closed; pivot theorem open. |
| Section 10.4 prose | Complex matrices `B+iC` have growth factor `< 3` | SKIP | Later deferred block also has Split 1 norm/complex gates | Citation-only lengthy external theorem in notes, not a Split 2 core target in this pass. |
| Notes, references, LAPACK | Historical notes, software routines, implementation descriptions | SKIP | No integrated previous-split blocker | Editorial/software-description material; no executable LAPACK semantics selected. |

## Not-Proved Ledger

| Source location | Exact selected claim | Current Lean status | Missing foundation | Next theorem |
| --- | --- | --- | --- | --- |
| Algorithm 10.2 and Theorems 10.3-10.4 | Concrete floating-point Cholesky loop generates the backward-error certificate | certificate interfaces only | Split 1 rounding/gamma/sqrt model plus concrete `fl_cholesky` trace | `fl_cholesky_backward_error_certificate` with all rounded updates accounted for |
| Theorems 10.5-10.7 | Demmel scaled Cholesky error and success/failure thresholds | interfaces/sign consequences only | Split 1 condition/eigenvalue/operator-norm foundations and concrete certificate generation | source-level Demmel diagonal bound and scaled perturbation theorem |
| Theorem 10.8 | Sun perturbation theorem | interface only | Split 1 operator norm/eigenvalue perturbation plus external proof route | local Sun perturbation theorem matching constants |
| Theorem 10.9(b), Lemmas 10.11/10.13, Problems 10.6-10.9 | Rank-r pivoted PSD Cholesky and complete-pivoting sensitivity | predicates/interfaces/witness pieces only | Split 1 rank/SVD/nullspace/minor/norm foundations and pivot trace | rank-r `PivotedCholeskySpec` construction and complete-pivoting inequality proof |
| Lemma 10.10 and Theorem 10.14 | Schur-complement perturbation and PSD Cholesky backward error | interfaces only | Split 1 norm/asymptotic inverse perturbation and full PSD algorithm trace | source-level Schur perturbation expansion with explicit remainder |
| Equation (10.29), Section 10.4 | Golub-Van Loan/Mathias nonsymmetric-positive-definite LU bounds | interface/equivalence only | Split 1 Frobenius/operator norm and condition-number foundations plus exact LU growth proof | `nonsym_pd_lu_growth_bound` without theorem-equivalent hypothesis |

## External Proof Sources

No new external proof-source acquisition was performed in this pass. The Chapter 10 PDF and Appendix A solutions supplied the proof routes for the newly closed exact rows. Citation-only source claims from Sun, Demmel, Golub-Van Loan, Mathias, and George-Ikramov-Kucherov remain advisory/open and are not used as hypotheses to close source rows.

## Hidden-Hypothesis Summary

- Newly closed rows have no theorem-equivalent hypotheses: the Section 10.1
  LDLT rewrite uses only an exact `CholeskyFactSpec`; Problem 10.1 uses only
  `IsSymPosDef`; Problem 10.4 uses only `IsSymPosDef`; Problem 10.8 witness is
  fully concrete.
- Certificate/interface rows intentionally expose missing source analysis as hypotheses and are not counted as full source closures.
- No orphan typeclass hypotheses were introduced.
- No vacuous definitions were introduced: the counterexample matrix and stopping criteria are source-facing objects; interfaces remain marked open when their hypotheses contain the analysis.

## Weak-Component and Bottleneck Summary

| Component | Why weak | Checks/status |
| --- | --- | --- |
| Section 10.1 Cholesky-to-LDLT rewrite | Cross-chapter closure could be overclaimed if only the Chapter 11 spec were referenced | Lean theorem constructs concrete `L`/`D` from `R`, proves unit-lower, diagonal block structure, identity permutation, and `A = L D L^T` from `CholeskyFactSpec.product_eq`. |
| Problem 10.1 off-diagonal/max-entry chain | Source-facing theorem and finite-sum algebra | Lean type checked; compared against Appendix A proof; axiom check reports only standard Lean/mathlib foundations. |
| Problem 10.4 exact GE growth chain | Reuses private exact Schur-complement proof, then proves local max-entry nonincrease and recursive positive-pivot invariant | Lean type checked; source statement is exact GE/no-row-exchange growth, not floating-point Cholesky rounding. |
| Problem 10.8 witness | Fixed counterexample and classification row | Lean type checked; compared against Appendix A example. |
| Certificate rows for Theorems 10.3-10.8/10.14 | Hypotheses contain missing analysis | Marked partial/current proof work; not counted as full source closure. |

Active bottleneck: full source-level floating-point Cholesky remains open on current proof/API work over integrated rounding/gamma/sqrt and norm/eigenvalue foundations plus a concrete `fl_cholesky` trace. Downstream theorem polishing is frozen until those listed foundations are exposed in source-facing form or proved locally in the appropriate module.

## Verification

Commands run in this pass:

- `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskySpec.lean` — passed.
- `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter10.lean` — passed.
- `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskySpec LeanFpAnalysis.FP.Algorithms.HighamChapter10 LeanFpAnalysis.FP.Algorithms` — passed; only pre-existing QR/FastMatMul linter warnings outside Chapter 10 were printed.
- `lake build` — passed (3476 jobs); only pre-existing QR/FastMatMul linter warnings outside Chapter 10 were printed.
- `lake env lean examples/LibraryLookup.lean` — failed with the default Lean thread stack while printing the large IEEE lookup section before the Chapter 10 block.
- `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/librarylookup_ch10_proof_completion.out 2>&1` — passed; output file has 70235 lines.
- Focused stdin lookup/axiom check for new Chapter 10 entries — passed.
- `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter10` — passed
  (3000 jobs) after adding the Section 10.1 Cholesky-to-LDLT rewrite.
- `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` — passed
  (3001 jobs), confirming the Chapter 10 import of the LDLT spec did not
  introduce an import cycle.
- `lake env lean --tstack=65536 examples/LibraryLookup.lean >
  /tmp/ch10_ldlt_librarylookup.out 2>&1` — passed; output file has 70716
  lines.
- `lake env lean TmpCh10LDLTAxioms.lean` — passed before removing the
  temporary axiom-check file.
- `lake build LeanFpAnalysis.FP.Algorithms` — passed (3423 jobs); only
  pre-existing QR/FastMatMul linter warnings outside Chapter 10 were replayed.
- Code-only `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b"` over `HighamChapter10.lean`, `CholeskySpec.lean`, and `examples/LibraryLookup.lean` — no matches.
- Code-only placeholder scan over `HighamChapter10.lean`,
  `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` — no `TODO`,
  `FIXME`, `placeholder`, or `by exact False.elim` matches. A broader
  `False.elim` scan hits the existing zero-dimensional induction branch in
  `higham10_problem_10_4_unpivoted_ge_positive_pivots_and_growth`, which is an
  impossible-index proof rather than placeholder misuse.
- Documentation/report scan found no unauthorized placeholders; the word
  `axiom` occurs only in verification prose.
- `git diff --check` — passed.

`#print axioms` for the new final-facing theorems reported only standard Lean/mathlib foundations:
`propext`, `Classical.choice`, and `Quot.sound`. Checked names included
`higham10_problem_10_1_abs_offdiag_lt_sqrt_diag_mul`,
`higham10_problem_10_1_maxEntryNorm_eq_largest_diag`,
`higham10_1_cholesky_to_ldlt`,
`spd_schur_complement_isSymPosDef`,
`higham10_problem_10_4_first_ge_maxEntryNorm_le`,
`higham10_problem_10_4_unpivoted_ge_positive_pivots_and_growth`, and
`higham10_problem_10_8_counterexample_not_psd`.

## Documentation

- Report path: `chapter_splitting/reports/chapter10_formalization_report.md`.
- Lookup files updated: `docs/LIBRARY_LOOKUP.md`, `examples/LibraryLookup.lean`.
- No theorem note or PDF generated.

## Open Issues

- Full Chapter 10 is not fully formalized.
- The concrete `fl_cholesky` algorithm, square-root/update rounding analysis, source spectral/norm perturbation theorems, rank-r pivoted PSD Cholesky, complete-pivoting/Kahan sharpness, and complex Hermitian Schur-complement/growth results remain open under the classifications above.
