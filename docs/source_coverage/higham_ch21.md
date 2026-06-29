# Higham Chapter 21 Source Coverage Ledger

## Source and Scope

- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002), verified from the SIAM chapter PDF metadata and the printed chapter pages.
- Chapter: 21, "Underdetermined Systems".
- Source file: `References/1.9780898718027.ch21.pdf`.
- Printed pages: 407-414.
- Mode: core.
- Parallel split: 4.
- Planning documents consulted: `chapter_splitting/HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md`, Split 4 section of `chapter_splitting/split_primary_contracts.md`, and the Chapter 21 rows of `chapter_splitting/chapter_index.md`.
- Source extraction: `pdftotext -layout` was used for navigation; rendered pages 408-412 were inspected for equations and theorem statements.
- Baseline: `lake env lean LeanFpAnalysis/FP/Algorithms/Underdetermined/UnderdeterminedSolve.lean` passed before Chapter 21 edits.
- Selected-scope gate: FAIL. The Chapter 21 core inventory is now visible, but the primary theorem surfaces are either unstarted or only represented by coarse existing predicates whose comments still cite Chapter 20 labels.
- Oracle status: no GPT Pro oracle consultation has been used for Chapter 21.

## Source Inventory

| ID | Source location | Kind | Statement summary | Precision | Generality | Source proof | Dependencies | Decision | Reason code | Lean artifact/status |
|---|---|---|---|---|---|---|---|---|---|---|
| H21.Eq21_1.qr_transpose | Section 21.1, p. 408, (21.1) | equation | QR factorization setup for `A^T` as an orthogonal factor times a stacked triangular block. | precise | general | not applicable | QR factorization infrastructure from Chapter 19 | FORMALIZE_DEPENDENCY | DEP-REQUIRED | Existing prose in `UnderdeterminedSpec.lean`; exact source-facing theorem not yet present. |
| H21.Eq21_2.y_coordinates | Section 21.1, p. 408, (21.2) | equation | Express `b = A x` through `Q^T x`, giving the triangular equation for the first coordinate block. | precise | general | complete | H21.Eq21_1.qr_transpose | FORMALIZE_DEPENDENCY | DEP-REQUIRED | Not yet source-facing. |
| H21.Eq21_3.q_method_min_norm | Section 21.1, p. 408, (21.3) | equation | Q-method formula for the minimum 2-norm solution, obtained by setting the free coordinate block to zero. | precise | general | complete | H21.Eq21_1.qr_transpose, triangular solve | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Partly represented by comments; no exact Lean theorem yet. |
| H21.Eq21_4.pseudoinverse_formula | Section 21.1, p. 408, (21.4) | equation | Rewrite the Q-method solution as `A^T (A A^T)^(-1) b = A^+ b`. | precise | general | complete | matrix multiplication, inverse, pseudoinverse/minimum-norm solution | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `MinNormSolution` captures a normal-equation predicate only; exact source theorem open. |
| H21.Eq21_5.sne_equations | Section 21.1, p. 408, (21.5) | equation | Seminormal equations `R^T R y = b`, followed by forming `x = A^T y`. | precise | general | not applicable | QR factorization, normal equations | FORMALIZE_DEPENDENCY | DEP-REQUIRED | Used informally by `sne_backward_error`; source-facing equation wrapper open. |
| H21.Thm21_1.demmel_higham | Section 21.2, p. 409, Theorem 21.1 | theorem | Componentwise perturbation bound for the minimum 2-norm solution under `|Delta A| <= eps E`, `|Delta b| <= eps f`, including attainability up to a dimension-dependent factor for Holder norms. | precise with asymptotic remainder | general | sketch | pseudoinverse, projector, absolute norms, perturbation expansion | FORMALIZE_CORE | CORE-NAMED-RESULT | Existing `DemmelHighamPerturbation` is a coarse predicate and comments cite Theorem 20.1; source theorem open. |
| H21.Eq21_6.demmel_higham_bound | Section 21.2, p. 409, (21.6) | equation | Printed first-order componentwise perturbation bound for Theorem 21.1. | precise with `O(eps^2)` | general | sketch | H21.Thm21_1.demmel_higham | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | No exact Lean theorem yet. |
| H21.Eq21_7.first_order_expansion | Section 21.2, p. 409, (21.7) | equation | First-order expansion for `y - x` in terms of the projector, `Delta A`, `Delta b`, and the pseudoinverse. | precise with `O(eps^2)` | general | complete sketch | H21.Thm21_1.demmel_higham | FORMALIZE_DEPENDENCY | DEP-REQUIRED | Open. |
| H21.Eq21_8.componentwise_special_case | Section 21.2, p. 409, (21.8) | equation | Special case of (21.6) with `E = |A|H` and `f = |b|`, using `cond2(A) = || |A^+| |A| ||_2`. | precise with `O(eps^2)` | general | sketch | H21.Eq21_6.demmel_higham_bound, condition measure | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open. |
| H21.Eq21_9.normwise_special_case | Section 21.2, p. 409, (21.9) | equation | Normwise specialization of (21.6), with `(mn)^(1/2) kappa_2(A)` dependence. | precise with `O(eps^2)` | general | sketch | H21.Eq21_6.demmel_higham_bound, normwise perturbation | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open. |
| H21.Lem21_2.kielbasinski_schwetlick | Section 21.2, p. 410, Lemma 21.2 | lemma | Two differently perturbed occurrences of `A` in the normal-equation representation can be replaced by one perturbation, preserving the minimum-norm solution. | precise | general | complete | projector onto `x`, pseudoinverse perturbation bound, Lemma 20.6 analogy | FORMALIZE_CORE | CORE-NAMED-RESULT | Existing `KielbasinskiSchwetlickUndet` is a coarse Gram-system predicate and comments cite Lemma 20.2; source theorem open. |
| H21.Prose21_2.normwise_bound | Section 21.3 opening, p. 411 | precise prose | Lemma 21.2 gives `||Delta A||_p <= (||Delta A_1||_p^2 + ||Delta A_2||_p^2)^(1/2)` for `p = 2, F`. | precise | general | follows from lemma | H21.Lem21_2.kielbasinski_schwetlick | FORMALIZE_CORE | CORE-PRECISE-PROSE | Coarsely mirrored in `KielbasinskiSchwetlickUndet`; exact source theorem open. |
| H21.Thm21_3.sun_sun_etaF | Section 21.2, p. 411, Theorem 21.3 | theorem | Normwise Frobenius backward error formula for an arbitrary approximate minimum 2-norm solution, including the zero-vector case and the nonzero formula involving `theta`, residual norm, and the smallest singular value of `A(I - y y^+)`. | precise | general | citation-only | Chapter 20 normwise backward-error machinery, pseudoinverse projector, singular values | FORMALIZE_CORE | CORE-NAMED-RESULT | Open; likely should reuse/extend `LSQRSolve.lean` normwise backward-error infrastructure. |
| H21.Def21_3.rowwise_backward_error | Section 21.3, p. 411 | definition | Row-wise backward error for a minimum-norm underdetermined system, requiring the perturbed solution to remain minimum norm. | precise | general | not applicable | row-wise perturbation model, minimum-norm solution predicate | FORMALIZE_DEPENDENCY | DEP-REQUIRED | Open. |
| H21.Thm21_4.q_method_backward_stable | Section 21.3, pp. 411-412, Theorem 21.4 | theorem | Under a smallness condition, the Q method computes a solution that is the minimum 2-norm solution to a row-wise perturbed system with row perturbations bounded by a gamma factor. | precise but implementation-facing | general | sketch | Chapter 19 QR stability, Lemma 19.3, H21.Lem21_2.kielbasinski_schwetlick | FORMALIZE_CORE | CORE-NAMED-RESULT | Existing `QMethodBackwardStable` is a coarse Gram-system predicate and comments cite Theorem 20.3; source theorem open. |
| H21.Eq21_10.computed_q_action | Section 21.3, p. 412, (21.10) | equation | Computed solution formation by a perturbed orthogonal action on the stacked vector, with Frobenius bound on `Delta Q`. | precise | general | sketch | Lemma 19.3 / QR transformation application | FORMALIZE_DEPENDENCY | DEP-REQUIRED | Open. |
| H21.Eq21_11.forward_error_bound | Section 21.3, p. 412, (21.11) | equation | Forward error bound from Theorem 21.4 and (21.8), independent of row scaling through `cond2(A)`. | precise with `O(u^2)` | general | sketch | H21.Thm21_4.q_method_backward_stable, H21.Eq21_8.componentwise_special_case | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Existing `underdetermined_forward_error` proves a componentwise perturbation consequence for a Gram system; source theorem open. |
| H21.Prose21_3.sne_forward_not_backward | Section 21.3, p. 412 | precise prose / qualitative mix | The SNE method has the same form of forward bound but is not backward stable; only the seminormal equations have a small residual. | partly precise | general | citation-only | SNE residual model, Cholesky solve backward error | FORMALIZE_DEPENDENCY | DEP-REQUIRED | `sne_backward_error` and `sne_forward_error_matches_q_method` partially cover exact Gram-system consequences; source-facing status open. |
| H21.Table21_1.vandermonde_errors | Section 21.3, p. 413, Table 21.1 | table / empirical output | Reported backward-error values for an underdetermined Vandermonde example. | empirical | empirical run | none | machine details and exact routines unspecified | SKIP | SKIP-EMPIRICAL | Not encoded. |
| H21.Prose21_3.mgs_stable_formation | Section 21.3, p. 413 | algorithmic prose | Alternative MGS-based formation recurrence for `x = Qy`, with a cited stability claim. | precise algorithm, citation-only stability | general algorithm | citation-only | MGS QR infrastructure, stability proof from external source | BENCHMARK_CANDIDATE | BENCHMARK-COMPARISON | Not core for first Chapter 21 pass; candidate for later benchmark/stability work. |
| H21.Notes21_4 | Section 21.4, pp. 413-414 | notes and references | Bibliographic provenance for Theorems 21.1, 21.3, 21.4, SNE analysis, and MGS method. | editorial/citation | not applicable | not applicable | external proof-source lookup when selected proof source is needed | SKIP | SKIP-LITERATURE-REVIEW | Not encoded, but citations recorded when proof-source acquisition is triggered. |
| H21.LAPACK21_4_1 | Section 21.4.1, p. 414 | software note | LAPACK routine names for full-rank and rank-deficient underdetermined systems. | implementation note | machine/library specific | none | LAPACK semantics outside core mathematical model | SKIP | SKIP-MACHINE-SPECIFIC | Not encoded in core mode. |
| H21.Problem21_1 | Problems, p. 414 | problem | benchmark-reserved; statement not transcribed | precise | benchmark | not applicable | benchmark run only | BENCHMARK_CANDIDATE | BENCHMARK-RESERVED | Not encoded; problem-local displayed equations are also reserved and not transcribed here. |

## Existing Lean Surface

| Source concept/result | Existing declaration | File/module | Current status |
|---|---|---|---|
| Minimum-norm normal-equation predicate | `MinNormSolution` | `LeanFpAnalysis/FP/Algorithms/Underdetermined/UnderdeterminedSpec.lean` | Partial dependency. Captures Gram inverse and normal equations but not the full rectangular minimum-norm characterization from (21.3)-(21.4). |
| Theorem 21.1 coarse perturbation predicate | `DemmelHighamPerturbation` | `LeanFpAnalysis/FP/Algorithms/Underdetermined/UnderdeterminedSpec.lean` | Stale source label and coarse bound surface; useful only as a placeholder-like predicate, not a source theorem closure. |
| Lemma 21.2 coarse symmetrization predicate | `KielbasinskiSchwetlickUndet` | `LeanFpAnalysis/FP/Algorithms/Underdetermined/UnderdeterminedSpec.lean` | Stale source label and Gram-system abstraction; exact projector theorem remains open. |
| Theorem 21.4 coarse Q-method stability predicate | `QMethodBackwardStable` | `LeanFpAnalysis/FP/Algorithms/Underdetermined/UnderdeterminedSolve.lean` | Stale source label and coarse Gram-system abstraction; exact source theorem remains open. |
| SNE Gram-system backward error | `sne_backward_error` | `LeanFpAnalysis/FP/Algorithms/Underdetermined/UnderdeterminedSolve.lean` | Proved Cholesky-solve consequence for the Gram system; source-facing SNE status still open. |
| Gram-system forward perturbation consequence | `underdetermined_forward_error` | `LeanFpAnalysis/FP/Algorithms/Underdetermined/UnderdeterminedSolve.lean` | Proved componentwise bound for perturbed Gram system; does not close (21.11). |
| SNE/Q forward-error bridge at Gram level | `sne_forward_error_matches_q_method` | `LeanFpAnalysis/FP/Algorithms/Underdetermined/UnderdeterminedSolve.lean` | Proved by reusing `underdetermined_forward_error`; source-facing row remains open. |

## Theorem-Design Plan

| Source target | Intended Lean work | Dependencies | Feasibility status | Next action |
|---|---|---|---|---|
| Source labels throughout existing underdetermined files | Correct comments/docstrings from Chapter 20 labels to Chapter 21 labels without changing theorem strength. | Existing compiling files | small-adapter | First Lean milestone. |
| Equations (21.3)-(21.4) | Add source-facing definitions/wrappers for the normal-equation minimum-norm predicate and pseudoinverse formula where local matrix infrastructure supports it. | `MinNormSolution`, `IsInverse`, `matMulVec` | small-adapter / missing rectangular API | Search MatrixAlgebra and LS infrastructure for reusable pseudoinverse/projector definitions. |
| Lemma 21.2 | Replace or supplement the coarse predicate with projector-level hypotheses and a proved source-facing structural wrapper where possible. | Projector algebra, vector dot/norm utilities, Chapter 20 Lemma 20.6 analogues | route-choice | Reuse Chapter 20 least-squares projector infrastructure before defining anything new. |
| Theorem 21.3 | Reuse the Chapter 20 normwise backward-error value-set/Frobenius-cost machinery to model the underdetermined minimum-norm feasible set and formula. | `LSQRSolve.lean` backward-error infrastructure, singular-value helpers | missing-foundation | Search for `etaF`, projector complement, and rectangular Frobenius lemmas before designing new declarations. |
| Theorem 21.4 and (21.11) | Package the existing Gram-system bounds more honestly, then expose missing QR/Lemma 21.2 foundations in a not-proved row rather than assuming them. | Chapter 19 QR stability, Lemma 21.2, row-wise backward error definition | partial foundation | After label cleanup, build the row-wise backward-error predicate and connect existing Q-method abstraction to it only at its actual strength. |

## Open Selected-Scope Items

| Source location | Exact selected claim/status | Current Lean status | Missing foundation | Next concrete theorem |
|---|---|---|---|---|
| (21.1)-(21.5) | QR, Q-method, pseudoinverse, and SNE setup equations. | partial comments/predicates only | rectangular QR block algebra and source-facing wrappers | `underdetermined_q_method_normal_equations_of_qr` or smaller wrappers around `MinNormSolution`. |
| Theorem 21.1 and (21.6)-(21.9) | Componentwise perturbation theorem and two special cases. | coarse predicate only | pseudoinverse/projector perturbation expansion with `O(eps^2)` accounting | `undet_demmel_higham_first_order_expansion` or documented conditional surrogate. |
| Lemma 21.2 and normwise bound | Kielbasinski-Schwetlick symmetrization with projector construction and p-norm bound. | coarse Gram predicate only | rectangular perturbation projector theorem | `undet_symmetrized_perturbation_projector`. |
| Theorem 21.3 | Sun-Sun normwise backward-error formula. | unstarted | underdetermined minimum-norm feasible set and `sigma_m(A(I-y y^+))` branch | `undetNormwiseBackwardErrorEtaF` definitions and zero-case theorem. |
| Row-wise backward error definition | Minimum-norm row-wise backward error. | unstarted | row-wise perturbation predicate tied to minimum-norm solution | `UndetRowwiseBackwardErrorFeasible`. |
| Theorem 21.4, (21.10), (21.11) | Q method row-wise backward stability and forward-error consequence. | coarse Q-method predicate and Gram forward consequence only | Chapter 19 QR computed factorization route, Lemma 21.2 exact bridge, row-wise predicate | source-facing wrapper at actual current strength, then close foundations one by one. |

## Skipped, Deferred, and Benchmark-Reserved Items

| Source location | Summary | Decision | Reason code | Notes |
|---|---|---|---|---|
| Table 21.1 | Reported floating-point backward errors for one Vandermonde experiment. | SKIP | SKIP-EMPIRICAL | Machine/run details are not specified sufficiently for core formalization. |
| Section 21.4 | Bibliographic notes and provenance. | SKIP | SKIP-LITERATURE-REVIEW | Use only for proof-source acquisition when needed. |
| Section 21.4.1 | LAPACK routine discussion. | SKIP | SKIP-MACHINE-SPECIFIC | Software note, not a core mathematical theorem. |
| Problem 21.1 | benchmark-reserved; statement not transcribed | BENCHMARK_CANDIDATE | BENCHMARK-RESERVED | Do not encode problem statement or problem-local equations during chapter formalization. |

## Verification This Pass

- `pdfinfo References/1.9780898718027.ch21.pdf`: 8 pages, title metadata for Chapter 21.
- `pdftotext -layout References/1.9780898718027.ch21.pdf /tmp/higham_ch21/ch21.txt`: succeeded; 438 extracted lines.
- Rendered PDF pages 2-6 with `pdftoppm`; visually inspected pages 2-5 for formulas (21.1)-(21.11).
- `lake env lean LeanFpAnalysis/FP/Algorithms/Underdetermined/UnderdeterminedSolve.lean`: passed before edits.

