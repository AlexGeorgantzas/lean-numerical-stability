# Higham Chapter 12 Formalization Report

## Source and scope

- Edition: Accuracy and Stability of Numerical Algorithms, 2nd ed. (SIAM PDF metadata/title verified from `References/1.9780898718027.ch12.pdf`; ISBN-style repository filename matches the second edition).
- Chapter: 12, Iterative Refinement.
- Printed pages: 231-243. PDF pages: 14.
- Source file: `References/1.9780898718027.ch12.pdf`.
- Appendix source read: `References/1.9780898718027.appa.pdf`, printed p. 556 for Problems 12.1-12.2 solutions. No Appendix A solutions are listed for Problems 12.3-12.5 in `chapter_index.md`.
- Mode: core / proof-completion for Split 2.
- Parallel split: 2.
- Planning documents consulted: `chapter_splitting/HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md`, Split 2 section of `chapter_splitting/split_primary_contracts.md`, and Chapter 12 / Appendix A rows of `chapter_splitting/chapter_index.md`.
- Selected-scope gate: FAIL for full-source Chapter 12 theorem closure. Exact local subclaims and Problem 12.1 are closed, but Theorems 12.1, 12.2, and the full source form of Theorem 12.4 use qualitative/asymptotic conditions not precise enough to close as stated.

## Implementation summary

New source-facing module:

- `LeanFpAnalysis/FP/Algorithms/HighamChapter12.lean`

Updated navigation:

- `LeanFpAnalysis/FP/Algorithms.lean`
- `docs/LIBRARY_LOOKUP.md`
- `examples/LibraryLookup.lean`

The existing reusable module `LeanFpAnalysis/FP/Algorithms/IterativeRefinement.lean` already contained genuine proofs of one-step residual identities, residual bounds, update-rounding bounds, correction bounds, linear contraction, and conditional backward-error conclusions. This pass added accurate Chapter 12 labels and one new local proof for Problem 12.1.

## Source inventory and decision ledger

| ID | Source location | Kind | Statement summary | Precision | Source proof | Dependencies | Classification | Previous-split dependency | Lean artifact/status |
|---|---|---|---|---|---|---|---|---|---|
| C12-intro-steps | p. 232 intro | Algorithmic prose | Iterative refinement steps `r=b-Ax`, solve `Ad=r`, update `y=x+d`. | precise abstract process; implementation details underspecified | prose | solver/residual/update model | CLOSED for abstract one-step semantics | No previous-split dependency | `higham12_3_exact_one_step_residual_bound`, `higham12_14_residual_identity`, reused `thm_11_3_identity` |
| Eq12.1 | p. 232 | Model assumption | Solver satisfies `(A+DeltaA)y=c`, `|DeltaA| <= u W`. | precise as abstract contract | none | none | CLOSED | No previous-split dependency | `higham12_1_SolverWBound` |
| Eq12.2 | p. 233 | Numbered inequality | Residual perturbation bound after rewriting by exact solution. | precise once raw residual bound is supplied | derivation in text | componentwise finite sums | CLOSED | No previous-split dependency | New proof `higham12_2_residual_delta_bound` |
| Eq12.3 | p. 233 | Numbered asymptotic estimate | `|F_i| <= u |A^-1| W + O(u^2)`. | partly precise; `O(u^2)` and inverse perturbation route unstated | sketch | inverse/Neumann, componentwise matrix abs | WAIT-PREVIOUS-SPLIT | Yes, direct previous-split dependency: Split 1 `H06.norms`/`H06.condition_distance` plus exact asymptotic/Neumann infrastructure; should not be redefined locally because Split 1 owns norm/inverse foundation | Open; exact resolver-based subclaim reused via `higham12_20_correction_via_resolver` |
| Eq12.4 | p. 233 | Numbered identity | `d_i = (I+F_i) A^-1 r_i = ...`. | partly precise because `F_i` is introduced through asymptotic Eq12.3 | derivation | Eq12.3 | WAIT-PREVIOUS-SPLIT | Yes, indirect previous-split dependency through Eq12.3 | Open as full source identity; one-step residual identity closed separately |
| Eq12.5 | p. 233 | Numbered recurrence | Componentwise forward-error recurrence `|x_{i+1}-x| <= G_i|x_i-x| + g_i`. | partly precise; exact first display precise, later estimates use `approx`/`<~` | derivation | Eq12.2-Eq12.4, inverse/norm tools | WAIT-PREVIOUS-SPLIT | Yes, indirect previous-split dependency through Eq12.3 and Split 1 inverse/norm foundation | Exact scalar contraction skeleton closed by `higham12_forward_error_linear_contraction` and `higham12_forward_error_steady_state` |
| Thm12.1 | p. 234 | Theorem | Mixed precision refinement reduces forward error by factor approximately `eta` until relative error approximately `u`. | underspecified: "sufficiently less than 1", "approximately" | summary of Eq12.5 | Eq12.5, gamma/norm foundation | SKIP | Yes, indirect previous-split gate if made precise through Eq12.5; primary reason is missing precise statement | Exact contraction theorem closed as replacement skeleton, not full theorem |
| Eq12.6 | p. 234 | Numbered equation | LU specialization `uW == gamma_3n |Lhat||Uhat|`. | precise as reference to Theorem 9.4 but depends on computed LU semantics | citation to Theorem 9.4 | Chapter 9 LU solve backward error | CLOSED as reused Split-2 contract shape | No previous-split dependency | Reused `lu_solve_to_solver_bound`, `lu_refinement_backward_stable`, Chapter 9 `higham9_4_lu_solve_backward_error` |
| Thm12.2 | p. 234 | Theorem | Fixed precision refinement reduces error by factor approximately `eta` until `<~ 2n cond(A,x)u`. | underspecified: approximate factor and `<~` | summary of Eq12.5 | Eq12.5, componentwise condition theory | SKIP | Yes, indirect previous-split gate if made precise through Eq12.5/H06; primary reason is missing precise statement | Exact contraction skeleton closed, not full theorem |
| Eq12.7 | p. 235 | Model assumption | Initial residual bound `|b-A xhat| <= u(g(A,b)|xhat| + h(A,b))`. | precise abstract contract | none | none | CLOSED | No previous-split dependency | `higham12_7_initialResidualBound` |
| Eq12.8 | p. 235 | Model assumption | Computed residual accuracy `|rhat-r| <= u t(A,b,xhat)`. | precise abstract contract | none | none | CLOSED | No previous-split dependency | `higham12_8_residualComputationBound` |
| Eq12.9 | p. 235 | Numbered equation | Conventional residual bound using `gamma_{n+1}`. | precise | reference to Ch3 matvec residual analysis | Split 1 gamma/matvec model | CLOSED relying on previous split result | Yes, direct previous-split reliance on available `H03.gamma_theta`/matvec infrastructure | `higham12_9_conventional_residual_error`, reused `conventional_residual_error` |
| Thm12.3 | p. 235 | Theorem | One step of refinement gives residual bound with `q=O(u)` under a Lipschitz-like condition. | partly precise; exact residual identity is precise, final `O(u)` statement underspecified | proof sketch | Eq12.7-Eq12.14, asymptotics | CLOSED for exact non-asymptotic bound; SKIP for `q=O(u)` conclusion | No previous-split dependency for exact bound; asymptotic prose has no previous-split blocker but lacks precise statement | `higham12_3_exact_one_step_residual_bound`, `higham12_14_residual_identity`, `higham12_14_residual_bound`; full `O(u)` row left open by policy |
| Eq12.10 | p. 235 | Numbered asymptotic bound | `|b-Ay| <= u(h(A,rhat)+t(A,b,y)+|A||y|+u q)`. | partly precise; `q=O(u)` not formalized | proof sketch | Eq12.14 and asymptotic assumptions | SKIP | No previous-split dependency | Exact Eq12.14 theorem formalized instead |
| Eq12.11 | p. 236 | Numbered inequality | Original residual satisfies Eq12.7 instance. | precise as assumption | immediate from Eq12.7 | Eq12.7 | CLOSED | No previous-split dependency | `higham12_7_initialResidualBound` |
| Eq12.12 | p. 236 | Numbered equation/inequality | Correction solve residual form `A d = rhat + f1`, `|f1| <= u(...)`. | precise as abstract assumption | from solver assumption | solver model | CLOSED as theorem input/adapter | No previous-split dependency | `higham12_3_exact_one_step_residual_bound`, reused `solver_perturbation_to_residual` |
| Eq12.13 | p. 236 | Numbered equation/inequality | Rounded update `y=xhat+dhat+f2`, `|f2| <= u(|xhat|+|dhat|)`. | precise as abstract update model | none | FP addition model if instantiated | CLOSED as theorem input and derived bound | No previous-split dependency | `higham12_17_update_bound`, `higham12_17_update_bound_div` |
| Eq12.14 | p. 236 | Numbered identity/bound | Residual decomposition and three-term bound. | precise | complete | finite-sum algebra | CLOSED | No previous-split dependency | `higham12_14_residual_identity`, `higham12_14_residual_bound`, `higham12_3_exact_one_step_residual_bound` |
| Scaling sigma def | p. 236 | Definition | `sigma(B,x)=max_i(|B||x|)_i/min_i(|B||x|)_i`. | precise when denominator positive | none | finite sup/inf | CLOSED | No previous-split dependency | Reused `skewnessRatio`; new `higham12_vectorAbsSkew` for Problem 12.1 |
| Thm12.4 | pp. 236-238 | Theorem | Under conditions involving an approximate function `f`, get `|b-Ay| <= 2 gamma_{n+1}|A||y|`. | partly precise; `f(t1,t2) approx ...` and sufficient condition are not exact | long sketch | Eq12.15-Eq12.22, inverse/norm/Neumann/asymptotic infrastructure | SKIP for full source theorem; CLOSED for exact conditional conclusion | Yes, indirect previous-split gate for a precise version through H06 inverse/norm/asymptotic foundation; main reason is missing precise `f` | `higham12_4_conditional_two_gamma_bound` proves exact conclusion from explicit dominance hypothesis |
| Eq12.15 | p. 237 | Numbered inequality | First specialized residual bound with `G,H`. | partly precise; derived after using Eq12.9 and source assumptions | sketch | Eq12.14, Eq12.9 | WAIT-PREVIOUS-SPLIT | Yes, indirect previous-split reliance via Eq12.9/gamma and matrix coefficient infrastructure | Partially represented by `higham12_19_combined_coefficients`; full G/H matrix form open |
| Eq12.16 | p. 237 | Numbered approximation | Simplified bound after replacing `b` by zero and approximating `gamma+u`. | underspecified/asymptotic | informal | Eq12.15 | SKIP | No direct previous-split dependency; skipped because source explicitly uses approximation and modeling replacement | Not formalized as exact theorem |
| Eq12.17 | p. 237 | Numbered inequality | Update rounding implies bound on `|xhat|`. | precise | derivation | Eq12.13 | CLOSED | No previous-split dependency | `higham12_17_update_bound`, `higham12_17_update_bound_div` |
| Eq12.18 | p. 237 | Numbered inequality | Bound `|rhat|` after dropping `|b|` terms and using Eq12.17. | partly precise; term dropping tied to simplification | sketch | Eq12.11, Eq12.17 | CLOSED for exact no-dropping variant | No previous-split dependency for exact variant | `higham12_18_residual_abs_bound` |
| Eq12.19 | p. 237 | Numbered inequality/definition | Combined residual bound defining `M1`, `M2`. | partly precise; exact after G/H setup | sketch | Eq12.16-Eq12.18 | CLOSED for scalar coefficient variant | No previous-split dependency for exact variant | `higham12_19_combined_coefficients` |
| Eq12.20 | p. 238 | Numbered inequality | Correction bound before Neumann inversion. | partly precise; uses `A^-1`, `M3`, `M4`. | sketch | inverse/norm foundation | WAIT-PREVIOUS-SPLIT | Yes, direct previous-split dependency on Split 1 H06 inverse/norm/Neumann infrastructure | Resolver form closed by `higham12_20_correction_via_resolver` |
| Eq12.21 | p. 238 | Numbered inequality | Correction bound after applying `(I-uM3)^-1`. | partly precise; Neumann inverse positivity and norm bound unstated | sketch | Eq12.20, Neumann series | WAIT-PREVIOUS-SPLIT | Yes, direct previous-split dependency on H06/Neumann nonnegative inverse foundation | Product form closed by `higham12_21_correction_product_bound` |
| Eq12.22 | p. 238 | Numbered inequality | Final residual bound with `M5`, then sigma-bound. | partly precise; depends on Problem 12.1 and approximate norm budget | sketch | Eq12.19-Eq12.21, Problem 12.1 | CLOSED for exact conditional two-gamma consequence | Yes, indirect previous-split gate for full source sufficient condition | `higham12_4_conditional_two_gamma_bound`; Problem 12.1 dependency closed |
| Tables12.1-12.3 | pp. 239-240 | Tables/experiments | Backward errors for GE/GEPP/QR on MATLAB/gallery matrices. | empirical source output | none | machine/library/random vector details | SKIP | No previous-split dependency | Skipped: empirical/machine-specific and random seed/library unspecified |
| Notes refs | pp. 240-242 | Notes/literature/software | Historical notes, LAPACK routine names, termination criteria, condition estimator discussion. | expository/implementation-specific | n/a | later chapters/software | SKIP | Some later-chapter references, but no selected theorem target | Skipped: literature review/software guidance |
| Problem12.1 | p. 242; App A p. 556 | Exercise | Prove `|A||x| <= sigma ||A||_inf |x|`. | precise after dimension-compatible square correction; printed rectangular version has dimension mismatch | complete Appendix solution | finite sup/inf and row-sum norm | CLOSED | No previous-split dependency | New proof `higham12_problem_12_1_square` plus skew lemmas |
| Problem12.2 | p. 242; App A p. 556 | Exercise | Use Section 12.1 to get GEPP one-step forward error bound under Theorem 12.4. | partly precise; Appendix proof uses `approx`, `<~`, "modest norm", and full Theorem 12.4 | sketch | Eq12.5, Theorem12.4, GEPP growth | SKIP | Yes, indirect previous-split gate if made precise via Eq12.5/H06; primary reason is qualitative/asymptotic proof statement | Not formalized; Problem 12.1 dependency closed |
| Problem12.3 | p. 242 | Exercise | Empirically investigate `|| |L||L^-1| ||_inf` for GEPP. | empirical | none | machine/data generation | SKIP | No previous-split dependency | Skipped empirical exercise |
| Problem12.4 | p. 242 | Exercise | Multiple right-hand side refinement with fast multiplication satisfying Eq13.4. | theoretical but depends on later split | none | Chapter 13 Eq13.4 fast multiplication | DEFER-LATER-SPLIT | No previous-split dependency; direct later-split dependency | Destination Split 3 / Chapter 13 |
| Problem12.5 | pp. 242-243 | Research problem | Ask whether one-step refinement suffices for Cholesky/diagonal pivoting. | research/open-ended | none | Cholesky/indefinite methods | SKIP | No previous-split dependency | Skipped: explicit research problem |

## Feasibility gate for selected targets

| Selected theorem/source | Intended Lean theorem | Required foundation | Status | Existing theorem/source | Smallest next Lean target | Downstream work allowed? |
|---|---|---|---|---|---|---|
| Thm12.1/12.2 exact contraction core | `higham12_forward_error_linear_contraction` | Scalar affine recurrence theorem | available-local | `linear_contraction` | closed | yes |
| Thm12.1/12.2 full source forms | exact theorem replacing "approximately", "<~", and "sufficiently less than 1" | precise constants and source-level theorem statement | out-of-scope-by-policy | none | author/reviewer must choose exact constants | no, full row skipped as underspecified |
| Eq12.3-Eq12.5 full matrix recurrence | exact Neumann/inverse perturbation and componentwise matrix inverse API | Split 1 H06 inverse/norm/asymptotic foundation | missing-foundation | partial resolver interfaces in `IterativeRefinement` | exact nonnegative Neumann inverse theorem for `I-uM` | no, full recurrence rows remain waiting |
| Thm12.3 exact algebraic part | `higham12_3_exact_one_step_residual_bound` | three-term residual identity and triangle bound | available-local | `thm_11_3_specialized` | closed | yes |
| Thm12.3 asymptotic `q=O(u)` | none | asymptotic model for vector-valued functions `t`, update/error sizes | out-of-scope-by-policy | none | exact asymptotic theorem with quantified filter | no, skipped as underspecified |
| Thm12.4 exact conclusion from explicit dominance | `higham12_4_conditional_two_gamma_bound` | one-step residual bound | available-local | `refinement_two_gamma_bound` | closed | yes |
| Thm12.4 full source sufficient condition | exact `f(t1,t2)` and proof of dominance | Split 1 H06 inverse/norm/Neumann plus precise constants | missing-foundation / missing precise statement | none | exact `M5` norm/sigma theorem with chosen `f` | no, full row skipped/waiting |
| Problem12.1 | `higham12_problem_12_1_square` | finite max/min and row-sum infinity norm | available-local | `row_sum_le_infNorm` | closed | yes |
| Problem12.4 | deferred theorem using fast multiplication Eq13.4 | Chapter 13 fast-multiplication error contract | missing-foundation | none in Split 2 | Split 3 Eq13.4 implementation | no, defer to Split 3 |

## Completed selected targets

| Source label | Lean declaration | File | Theorem surface | Notes |
|---|---|---|---|---|
| Eq12.1 | `higham12_1_SolverWBound` | `LeanFpAnalysis/FP/Algorithms/HighamChapter12.lean` | abstract solver perturbation contract | Source model definition, not a theorem. |
| Eq12.2 | `higham12_2_residual_delta_bound` | same | exact componentwise residual perturbation inequality | New proof, no hidden theorem-equivalent hypothesis beyond raw residual model. |
| Eq12.3-Eq12.5 exact contraction skeleton | `higham12_forward_error_linear_contraction`, `higham12_forward_error_steady_state` | same | scalar affine recurrence and steady-state bound | Reused exact local theorem; does not close approximate full Theorems 12.1/12.2. |
| Eq12.7 | `higham12_7_initialResidualBound` | same | abstract initial residual model | Source assumption modeled honestly. |
| Eq12.8 | `higham12_8_residualComputationBound` | same | abstract computed residual model | Source assumption modeled honestly. |
| Eq12.9 | `higham12_9_conventional_residual_error` | same | conventional residual bound | Reuses already available FP/matvec proof. |
| Thm12.3 exact core / Eq12.14 | `higham12_3_exact_one_step_residual_bound`, `higham12_14_residual_identity`, `higham12_14_residual_bound` | same | exact residual identity and residual bound | Genuine finite-sum proof chain via `thm_11_3_*`. |
| Eq12.17 | `higham12_17_update_bound`, `higham12_17_update_bound_div` | same | update-rounding inequality | Reuses genuine proof `eq_11_15`. |
| Eq12.18 exact variant | `higham12_18_residual_abs_bound` | same | residual absolute bound without source term-dropping | Reuses genuine proof `eq_11_16`. |
| Eq12.19 scalar-coefficient variant | `higham12_19_combined_coefficients` | same | combined residual bound | Reuses genuine proof `eq_11_17`. |
| Eq12.20-Eq12.21 resolver/product forms | `higham12_20_correction_via_resolver`, `higham12_21_correction_product_bound` | same | exact conditional correction bounds | Conditional on explicit resolver, not counted as full Neumann proof. |
| Thm12.4 conditional conclusion / Eq12.22 | `higham12_4_conditional_two_gamma_bound` | same | exact two-gamma residual bound from dominance hypothesis | Genuine transfer proof; full source sufficient condition remains open. |
| Problem12.1 square form | `higham12_vectorAbsSkew`, `higham12_vectorAbsSkew_nonneg`, `higham12_vectorAbsSkew_entry_bound`, `higham12_problem_12_1_square` | same | dimension-compatible Appendix solution theorem | New proof. The printed rectangular wording is recorded as a modeling correction. |

## Reused from repository or Mathlib

| Source concept/result | Existing declaration | File/module |
|---|---|---|
| Conventional residual computation | `conventional_residual_error` | `LeanFpAnalysis.FP.Algorithms.IterativeRefinement` |
| One-step residual identity and bound | `thm_11_3_identity`, `thm_11_3_bound`, `thm_11_3_specialized` | `LeanFpAnalysis.FP.Algorithms.IterativeRefinement` |
| Update-rounding bound | `eq_11_15`, `eq_11_15_div` | `LeanFpAnalysis.FP.Algorithms.IterativeRefinement` |
| Residual absolute bound | `eq_11_16` | `LeanFpAnalysis.FP.Algorithms.IterativeRefinement` |
| Combined coefficient bound | `eq_11_17` | `LeanFpAnalysis.FP.Algorithms.IterativeRefinement` |
| Correction resolver/product bounds | `eq_11_18`, `correction_product_bound` | `LeanFpAnalysis.FP.Algorithms.IterativeRefinement` |
| Conditional two-gamma residual bound | `refinement_two_gamma_bound` | `LeanFpAnalysis.FP.Algorithms.IterativeRefinement` |
| Linear contraction | `linear_contraction`, `linear_contraction_steady_state` | `LeanFpAnalysis.FP.Algorithms.IterativeRefinement` |
| Matrix infinity row-sum bound | `row_sum_le_infNorm` | `LeanFpAnalysis.FP.Analysis.MatrixAlgebra` |

## New dependencies

| Declaration | Why needed | Used by | Feasibility status |
|---|---|---|---|
| `higham12_vectorAbsSkew` | Source max/min ratio in Problem 12.1 | `higham12_problem_12_1_square` | closed |
| `higham12_vectorAbsSkew_nonneg` | Nonnegativity of the max/min ratio | Problem 12.1 proof | closed |
| `higham12_vectorAbsSkew_entry_bound` | Appendix solution step `||x||_inf e <= sigma |x|` | Problem 12.1 proof | closed |

## Hidden-hypothesis audit

Final-facing theorem hypotheses are source/model/domain hypotheses:

- `higham12_2_residual_delta_bound`: assumes the raw residual perturbation model and exact solution equation `Ax=b`; these are source assumptions, not the conclusion.
- `higham12_3_exact_one_step_residual_bound`: assumes explicit solver residual, residual computation, and rounded update bounds; conclusion is the combined residual bound, so no source theorem is assumed.
- `higham12_4_conditional_two_gamma_bound`: assumes the explicit dominance inequality. This is a conditional transfer theorem and is not counted as full Theorem 12.4 closure.
- `higham12_problem_12_1_square`: assumes nonzero vector components so the source max/min ratio is defined; this is a domain assumption.

Answers to the hidden-hypothesis audit:

- Target conclusion or equivalent missing theorem assumed? No for closed rows. The dominance hypothesis in `higham12_4_conditional_two_gamma_bound` is intentionally exposed and the full Theorem 12.4 row remains open.
- Stability/correctness result assumed when it should be proved? No closed row claims full stability beyond explicit hypotheses.
- Exact arithmetic assumed for computed quantities? Only abstract source contracts are stated; implementation-facing full computed paths are not claimed.
- Conditional/different-object result falsely closes stronger source row? No. The report keeps full Theorems 12.1, 12.2, 12.3 asymptotic part, and 12.4 source condition visible.
- Report says more than Lean proves? No.

No orphan classes are used as hypotheses. No vacuous definitions were added; new definitions model source contracts or the Problem 12.1 skewness ratio.

## Weak components and bottlenecks

| Component | Why weak | Checks | Evidence | Status |
|---|---|---|---|---|
| `higham12_2_residual_delta_bound` | componentwise algebra with finite sums | Lean typecheck; source comparison Eq12.2 | target statement matches exact displayed inequality with raw residual model | passed |
| `higham12_3_exact_one_step_residual_bound` | could be overread as full asymptotic Theorem 12.3 | Lean typecheck; report explicitly separates `O(u)` row | theorem only proves exact Eq12.14-style bound | passed |
| `higham12_4_conditional_two_gamma_bound` | conditional transfer near a major theorem | Lean typecheck; source comparison; hidden-hypothesis audit | dominance hypothesis visible; full theorem not counted closed | passed |
| `higham12_problem_12_1_square` | source has apparent rectangular/square mismatch | rendered PDF and Appendix p. 556 checked; theorem docstring notes dimension-compatible form | proof matches Appendix chain for square-compatible RHS | passed |

Active bottlenecks:

- Full Eq12.3-Eq12.5 / Theorems 12.1-12.2 require precise replacement of asymptotic and approximate source conditions plus Split 1 inverse/norm/Neumann foundation.
- Full Theorem 12.4 requires an exact function `f`, exact constants, and a proved route from the source condition to the dominance hypothesis.

## Not formalized because of previous-split dependency

| Source label/name | Direct or indirect previous-split dependency | Previous split | Contract family or missing result | Why not reproved locally | Next expected upstream theorem/interface |
|---|---|---|---|---|---|
| Eq12.3 | direct | Split 1 | `H06.norms`, `H06.condition_distance`, exact inverse perturbation / Neumann-series bound with componentwise absolute matrices and asymptotic remainder | Split 1 owns norm/inverse foundations; local redefinition would duplicate upstream matrix-norm API | Nonnegative Neumann inverse/resolvent theorem and exact inverse perturbation bound |
| Eq12.4 | indirect through Eq12.3 | Split 1 | Same as Eq12.3 | Depends on the unclosed `F_i` inverse perturbation object | Exact theorem deriving `d_i` representation from Eq12.3 |
| Eq12.5 full matrix recurrence | indirect through Eq12.3-Eq12.4 | Split 1 | Same as Eq12.3 plus componentwise matrix recurrence/norm bridge | Full recurrence should be built on shared inverse/norm infrastructure | Exact `G_i,g_i` recurrence theorem |
| Eq12.15 full G/H form | indirect | Split 1 | Gamma/matvec residual and matrix coefficient/norm bridge | Available gamma result reused, but full G/H coefficient calculus depends on upstream norm matrix API | Exact G/H coefficient substitution theorem |
| Eq12.20 | direct | Split 1 | H06 inverse/norm/Neumann infrastructure | It is a nonnegative inverse/resolvent theorem, not Chapter 12 local algebra | Theorem resolving `(I-uM3)^-1` positivity and norm bound |
| Eq12.21 | direct | Split 1 | Same Neumann infrastructure | Same reason | Exact correction bound with `(I-uM3)^-1` |
| Full Thm12.4 sufficient condition | indirect | Split 1 | Eq12.20-Eq12.21 plus exact sigma/norm bridge | Full proof should instantiate shared inverse/norm theory rather than local placeholders | Exact `M5` norm bound leading to `2 gamma` |

## Not formalized for another reason

| Source label/name | Classification | Previous-split dependency status | Exact reason | Destination if deferred |
|---|---|---|---|---|
| Thm12.1 full source statement | SKIP | Indirect previous-split gate would arise after precision repair | Uses "sufficiently less than 1" and "approximately"; no exact theorem statement | none |
| Thm12.2 full source statement | SKIP | Indirect previous-split gate would arise after precision repair | Uses "approximately" and `<~`; no exact theorem statement | none |
| Eq12.10 / Thm12.3 `q=O(u)` part | SKIP | No direct previous-split dependency | Vector-valued Big-O and assumptions on `t` not stated precisely enough | none |
| Eq12.16 | SKIP | No direct previous-split dependency | Source explicitly replaces `b` by zero and approximates coefficients; not an exact theorem | none |
| Tables 12.1-12.3 | SKIP | No previous-split dependency | Empirical MATLAB/gallery/random-vector outputs; machine/library/seed details unspecified | none |
| Notes and LAPACK prose | SKIP | No selected theorem dependency | Literature review and software routine discussion | none |
| Problem12.2 | SKIP | Indirect previous-split gate if exacted through Eq12.5/H06 | Appendix proof is asymptotic/qualitative (`approx`, `<~`, "modest norm") and depends on full Theorem 12.4 | none |
| Problem12.3 | SKIP | No previous-split dependency | Empirical investigation exercise | none |
| Problem12.4 | DEFER-LATER-SPLIT | No previous-split dependency | Depends on Chapter 13 Eq13.4 fast multiplication, owned by Split 3 | Split 3 / Chapter 13 |
| Problem12.5 | SKIP | No previous-split dependency | Explicit research problem | none |

## Verification

Commands run:

- `lake env lean LeanFpAnalysis/FP/Algorithms/IterativeRefinement.lean` - passed before edits.
- `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter12.lean` - passed after proof fixes.
- `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter12` - passed.
- `lake env lean LeanFpAnalysis/FP/Algorithms.lean` - passed after building the new module.
- `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter12 LeanFpAnalysis.FP.Algorithms` - passed. The build replayed only pre-existing QR/FastMatMul warnings outside Chapter 12.
- `lake env lean /tmp/ch12_axioms.lean` - passed; this focused lookup checked every new Chapter 12 source-facing declaration.
- `lake env lean examples/LibraryLookup.lean` - failed with the known pre-existing stack overflow in the IEEE `#check` section before the Chapter 12 entries. The focused Chapter 12 lookup above passed.
- `rg -n "\\b(sorry|admit|axiom|unsafe|opaque)\\b" LeanFpAnalysis/FP/Algorithms/HighamChapter12.lean` - no matches.
- `rg -n "\\b(sorry|admit|axiom|unsafe)\\b" LeanFpAnalysis examples` - no matches.
- `rg -n "TODO|FIXME|PROVE-NOW-SPLIT|WAIT-PREVIOUS-SPLIT|Chapter 12|chapter12|HighamChapter12" ...` - only intentional Chapter 12 ledger/navigation references; no stale TODO/FIXME or PROVE-NOW rows.
- `git diff --check` - passed.
- `lake build` - passed, 3477 jobs, with only pre-existing QR/FastMatMul warnings outside Chapter 12.

`#print axioms` results for final-facing new theorems:

- `higham12_2_residual_delta_bound`: `propext`, `Classical.choice`, `Quot.sound`.
- `higham12_3_exact_one_step_residual_bound`: `propext`, `Classical.choice`, `Quot.sound`.
- `higham12_4_conditional_two_gamma_bound`: `propext`, `Classical.choice`, `Quot.sound`.
- `higham12_vectorAbsSkew_entry_bound`: `propext`, `Classical.choice`, `Quot.sound`.
- `higham12_problem_12_1_square`: `propext`, `Classical.choice`, `Quot.sound`.

Placeholder scan result: no Lean code matches for `sorry`, `admit`, `axiom`, or `unsafe`.

## Documentation

- Inventory/report path: `chapter_splitting/reports/chapter12_formalization_report.md`.
- Library lookup path: `docs/LIBRARY_LOOKUP.md`.
- Executable lookup path: `examples/LibraryLookup.lean`.

## Open issues

- The source's Problem 12.1 is printed with `A in R^{m x n}` but the right-hand vector in both the problem and Appendix solution is `|x|`, which is only dimension-compatible with the row index in the square case. The Lean theorem records the square/dimension-compatible version and the report keeps the modeling decision visible.
- The existing reusable module `IterativeRefinement.lean` has legacy docstrings referring to "§11" and "Theorem 11.3/11.4" for the iterative-refinement material now used by Chapter 12. This Chapter 12 facade supplies accurate source-facing names; the legacy internal comments were not retitled in this pass to avoid broad churn.
