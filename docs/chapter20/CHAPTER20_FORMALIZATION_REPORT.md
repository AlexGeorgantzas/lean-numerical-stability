# Higham Chapter 20 Formalization Report

## Source and scope

- Edition: Nicholas J. Higham, *Accuracy and Stability of Numerical
  Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 20, “The Least Squares Problem.”
- Printed pages: 381-406; source PDF pages 1-26.
- Source file: `References/1.9780898718027.ch20.pdf`, SHA-256
  `7CA85D5CAF3FFD5AE90FB315E9B4E00912E174881BCF969E7BA0A7B3CE9EC814`.
- Appendix: Chapter 20 solutions, printed pp. 565-567, Appendix PDF pages
  39-41.
- Mode: core.
- Parallel split: 4; this chapter report covers the Chapter 20 slice of the
  full Chapters 20-28 plus Appendix A partition.
- Planning documents consulted: parallel blueprint, Split 4 primary contract,
  Chapter 20 index, and the chapter-formalization skill references.
- Inventory counts: 12 named results, 36 actually printed equation tags, 13
  Problems, and 11 Appendix solution rows.
- Selected-scope gate: **PASS (EXPLICIT-DOMAIN)**.

Every selected row is terminal. Implementation-facing theorems expose their
model-validity, local rounded-trace, and nonbreakdown domains; no conclusion is
silently weakened and no such domain is claimed for an arbitrary bare
`FPModel`.

## Split 4 repair outcome

The 2026-07-16 pass re-read all chapter and Appendix pages, checked the theorem
types rather than their names, corrected prior overclaims, and added concrete
source-strength improvements:

| Source label | Lean declaration | File | Theorem surface | Status |
|---|---|---|---|---|
| Theorem 20.5 / (20.20)-(20.21) | `theorem20_5_wks_finite_formula_and_eigenvalue`, `theorem20_5_wks_formula_eigenvalue_and_matrixOnly_limit` | `LSQRSolve.lean` | Arbitrary printed-shape least-squares data, `y != 0`, finite positive `theta`, minimizer/nonminimizer branches, and matrix-only limit | PASS |
| Theorem 20.4 total-perturbation surface | `LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_householderQRPanel_theorem20_4_printed_total_perturbations` | `Higham20Theorem20_4Absorption.lean` | Packages both actual `DeltaA_i`, the exact augmented system, one shared nonnegative Frobenius-unit witness, and the printed componentwise envelopes with an explicit dimension-only `lsTheorem20_4ConcreteGammaTildeTotal` | PASS (EXPLICIT-DOMAIN) |
| Equation (20.16) | `higham20_eq20_16_augmented_one_refinement_finite`, `higham20_eq20_16_augmented_one_refinement_actual_residual_update`, `higham20_eq20_16_actual_householderQR_one_refinement_finite` | `Higham20Equations.lean`, `Higham20Refinement.lean` | Proves the source residual chain, expands the gamma factors into the printed first-order terms plus an exact rational quadratic-and-higher remainder, instantiates the actual residual/update kernels, and separately connects the literal QR correction path to its implementation majorant | PASS; the formerly separate Theorem 20.4 upstream row is also closed |
| Theorem 20.9 / (20.27)-(20.28) | `GeneralizedQRFactorization.exists_theorem20_9_exact_householder` | `LSE.lean` | Unconditional GQR existence under the printed dimension inequalities; rank assumptions are separate | PASS |
| Cross-product example | `higham20CrossProductExample_symbolic_family` | `Higham20CrossProductExample.lean` | Symbolic `0 < epsilon < sqrt(u)` family, actual modeled rounded Gram, all-ones identity, singularity | PASS |
| p. 383 projector-complement identity | `higham20_fullColumn_range_projector_complement_complexMatrixOp2_eq_min_one_sub` | `Higham20Prose.lean` | Exact `||I-AA^+||_2 = min {1,m-n}` including square/tall cases | PASS |
| Theorem 20.7 rounded producer and pivot-position bound | `fl_pivotedStoredQR_returnedX_pivotPosition_of_roundedCoxHigham`, `fl_pivotedStoredQR_returnedX_exactMinimizer_of_roundedCoxHigham`, `roundedPolicy_exact_one_nonempty` | `Higham20Theorem20_7Contract.lean` | Runs the literal pivoted stored-QR, paired RHS, and `fl_backSub`; constructs the numerical contract from visible local trace budgets; returns the exact perturbed minimizer; and proves pivot-position matrix coefficient `16 gammaTilde` plus RHS coefficient `5 gammaTilde`. The older `sigmaCounter...` results remain to document the refuted exact-tail route. | PASS (EXPLICIT-DOMAIN) |
| Theorem 20.10, `p = 0` boundary | `Theorem20_10.computedX_emptyConstraints_partA_mixed_stability`, `Theorem20_10.computedX_emptyConstraints_partB_backward_error` | `Higham20Theorem20_10.lean` | Genuine rounded unconstrained branch; a source-rank threshold derives computed-`R` nonbreakdown | PASS (EXPLICIT-DOMAIN) |
| Theorem 20.10, `q = 0` boundary | `Theorem20_10.computedX_fullConstraints_partA_mixed_stability`, `Theorem20_10.computedX_fullConstraints_partB_backward_error` | `Higham20Theorem20_10.lean` | Genuine rounded constraint-only `B^T` Householder/forward-solve branch; source-rank threshold derives computed-`S` nonbreakdown | PASS (EXPLICIT-DOMAIN) |
| Elimination method / (20.30) | `Higham20EliminationActual.lseEliminationActualReducedSolution_is_reduced_minimizer`, `Higham20EliminationActual.lseEliminationActualReturnedSolution_isLSEMinimizer` | `Higham20EliminationActual.lean` | Constructs both exact pivoted QR stages, both solves, and the final returned LSE minimizer without assuming a reduced minimizer | PASS |
| Equation (20.19), Problem/Appendix 20.7 | `higham20_problem20_7_scaled_augmented_condition_extremum`, `higham20_problem20_7_square_scalar_branch_discrepancy` | `Higham20Equations.lean` | Full positive-scale extremum and printed bounds for `n<m`; exact scalar counterexample to the source's square-case lower envelope | PASS / SOURCE DISCREPANCY |
| p. 404 minimum-norm backward error | `lsMinimumNormBackwardErrorEtaF_eq_normwise_of_attained_injective`, `higham20_p404_square_source_discrepancy` | `Higham20MinimumNormBackwardError.lean` | Defines both infima, proves the immediate full-rank-at-an-attainer equality, and gives an exact nonzero-`b,y` square counterexample (`ordinary <= 1 < sqrt 2 <= strengthened`) | PASS / SOURCE DISCREPANCY: the cited Sun theorem is strict-tall and matrix-only; the printed unqualified square-or-tall extension is false |

The public README, library lookup, and Lean `#check` index now expose Chapter
20 entry points and link to this decision report.

## Named-result status

| Result | Status | Source-strength assessment |
|---|---|---|
| Theorem 20.1 | PASS | Full-column Wedin solution/residual bounds are local; qualitative approximate attainability remains attribution-only. |
| Theorem 20.2 | PASS | Printed componentwise and absolute-norm inequalities are local. |
| Theorem 20.3 | PASS (EXPLICIT-DOMAIN) | Actual Householder panel/RHS/back-substitution path with visible gamma and nonbreakdown assumptions. |
| Theorem 20.4 | PASS (EXPLICIT-DOMAIN) | The actual Householder panel/RHS/triangular-solve path produces both total perturbations, one common normalized witness, the printed matrix/RHS bounds, and the exact perturbed system under visible gamma-validity, full-rank, and computed-nonbreakdown assumptions. |
| Theorem 20.5 | PASS | The repair handles minimizer/nonminimizer branches and removes the former full-row-rank restriction that excluded genuinely tall source matrices. |
| Lemma 20.6 | PASS | Symmetric perturbation and Frobenius/operator-2 bounds. |
| Theorem 20.7 | PASS (EXPLICIT-DOMAIN) | Literal pivoted stored-QR/RHS/back-substitution endpoint with printed `alpha`/`beta`/`phi` scales, pivot-position `(j+1)^2`, and exact perturbed minimizer. Forward-row, compact-operation, multiplier-budget, gamma-validity, and diagonal nonbreakdown assumptions are visible. |
| Theorem 20.8 | PASS (EXPLICIT-DOMAIN) | Printed first-order coefficient plus explicit quadratic term on a source-only threshold. |
| Theorem 20.9 | PASS | Unconditional existence plus separate rank/nonsingularity equivalence. |
| Theorem 20.10 | PASS (EXPLICIT-DOMAIN) | Positive-block Part A/B plus genuine rounded `p=0,q>0` and `q=0,p>0` boundary branches are local; each boundary derives nonbreakdown from source rank and a roundoff threshold. |
| Lemma 20.11 | PASS | Arbitrary equal-rank Moore-Penrose surface, including rank zero. |
| Lemma 20.12 | PASS | Arbitrary equal-rank cross-projection equality and `min` bound. |

Detailed statuses for all 36 equation tags, every precise selected prose row,
all Problems, and all Appendix rows are in the source inventory.

## Reused from the repository and Mathlib

| Source concept | Existing declaration or module |
|---|---|
| Least-squares normal equations and exact minimizers | `LSQRSolve.lean` |
| Moore-Penrose certificates, ranks, singular values, and operator norms | `LSPerturbation.lean`, `Higham20MPProse.lean`, `Higham20Lemma20_11.lean`, `Higham20Lemma20_12.lean` |
| Householder QR panel/RHS transforms and triangular solves | `QR/*`, `Higham20Theorem20_3.lean`, `Cholesky/CholeskySolve.lean` |
| GQR/LSE algebra and exact Householder constructors | `LSE.lean` |
| Pivoted stored QR and Cox-Higham interfaces | `Higham20Theorem20_7*.lean` and Chapter 19 QR modules |
| Rounded MGS and repair interfaces | `Higham19Alg12MGSRounded.lean`, `Higham19Alg12MGSRepair.lean` |

No duplicate parallel least-squares API was introduced for the new results.

## New dependencies and active bottlenecks

| Declaration/dependency | Why needed | Used by | Feasibility status |
|---|---|---|---|
| Source-general rank proof for the WKS formula matrix | The printed Theorem 20.5 permits tall `A`; the old full-row-rank wrapper was impossible there | Theorem 20.5 finite formula/eigenvalue branches and matrix-only limit | Implemented and compiled |
| Exact zero-aware Householder GQR existence | Theorem 20.9 existence has no rank hypothesis | `GeneralizedQRFactorization.exists_theorem20_9_exact_householder` | Implemented and compiled |
| Corrected Cox-Higham rounded-feedback analysis | Theorem 20.7's printed row-local constants must come from an execution whose stage invariants account for rounded feedback | Replacement forward-row and rounded multiplier policies, compact-operation budgets, triangular-column transport, and exact minimizer assembly | Implemented and compiled; `sigmaCounter_no_coxHighamRowPolicy` remains as the formal reason the former exact-tail route was rejected |
| Total Theorem 20.4 perturbation absorption | The printed named theorem requires single-witness bounds for both total `DeltaA_i` | Theorem 20.4 | Implemented by transporting each triangular correction through the exact QR relation, summing the two nonnegative witnesses, and normalizing once |

## External proof sources

| Selected claim | Source and location | Role | Local Lean closure | Status |
|---|---|---|---|---|
| Theorem 20.1 | Wedin citation summarized in pp. 400-402 | Perturbation route and attainability attribution | Full-column inequalities local; stronger p. 402 sentence refuted by exact counterexample | ADOPTED/REJECTED AS CLASSIFIED |
| Lemma 20.12 | Stewart and Stewart-Sun citations on p. 400 | Cross-projection norm equality | Proved locally at arbitrary equal rank | ADOPTED |
| Theorem 20.5 | Walden-Karlson-Sun citation, pp. 392-393 | Backward-error/eigenvalue formula | Proved locally after source-generality repair | ADOPTED |
| Theorem 20.7 | Powell-Reid/Cox-Higham citation, p. 395 | Printed row-local producer | Reconstructed locally for the literal trace on explicit rounded-feedback and nonbreakdown conditions | ADOPTED AND PROVED (EXPLICIT-DOMAIN) |
| Theorem 20.8 | Elden/Cox-Higham citation, p. 396 | First-order LSE perturbation route | Proved locally on explicit source-only threshold | ADOPTED |
| Theorem 20.10 | Cox-Higham citation, pp. 398-399 | Rounded GQR stability | Positive-block path and both nontrivial empty-block boundary branches are proved locally on explicit source-rank/roundoff domains | ADOPTED |
| Difficult Theorem 20.7 audit | Oracle second-model consultation, slug `chapter20-theorem20-7-audit` | Independent source/type review and dependency-plan check | Its rejection of the earlier weaker endpoint and its pivot-position/rounded-feedback dependency outline were checked against the PDF and Lean types, then implemented locally | ADVISORY; VERIFIED DIAGNOSIS/PLAN ADOPTED |

## Skipped items

| Source location | Summary | Reason code |
|---|---|---|
| p. 381 and Section 20.11 | Epigraph, history, notes, and references | SKIP-EDITORIAL / SKIP-LITERATURE-REVIEW |
| p. 384 | “Less sensitive to row scaling” qualitative discussion | SKIP-QUALITATIVE |
| p. 405 | LAPACK routine catalogue | SKIP-PROGRAMMING-LANGUAGE |
| Problems 20.4, 20.6, 20.8 | Optional exercises not required by selected rows | OPTIONAL-PROBLEM-NOT-SELECTED |
| Problems 20.12-20.13 | Research problems without Appendix solutions | OPTIONAL-RESEARCH-PROBLEM |

## Empirical source outputs

| Source location | Printed output/claim | Missing machine details | Formal replacement | Status |
|---|---|---|---|---|
| pp. 390-391 | Refinement behavior and “nearly consistent” performance claim | Machine/base/precision/compiler/library/stopping rule/data/seed | Exact refinement step/run predicates | EXCLUDED EMPIRICAL |
| Table 20.1, pp. 393-394 | Vandermonde numerical values | MATLAB/platform/BLAS/LAPACK/precision/rounding/data generation | Exact WKS formula and algorithms | BENCHMARK CANDIDATE |
| p. 395 | Computed residual approximates minimizing componentwise residual | Dataset/method/pivot policy/precision/tolerance/seed | Exact backward-error definitions and conditional bounds | EXCLUDED EMPIRICAL |
| pp. 385-386, 398 | Operation counts | Counting convention, fused operations, memory traffic, architecture | Exact algorithm definitions | BENCHMARK CANDIDATE |

## Deferred items

| Source location | Summary | Destination/dependency | Reason |
|---|---|---|---|
| (20.14), p. 387 | Normal-equations forward bound with unspecified `c_mn` and `lesssim` | Future quantitative refinement if a precise constant is chosen | DEFER-MISSING-PRECISE-STATEMENT |
| pp. 391-392 | Mixed-precision and rough CSNE forward-error prose | Earlier refinement/Bjorck analyses | DEFER-MISSING-PRECISE-STATEMENT |
| p. 386; Problem/Appendix 20.5 | Qualitative MGS stability attribution and optional exercise with unspecified `c_{m,n} u` coefficient | Existing literal rounded-MGS and transfer theorems are retained as extra coverage | ATTRIBUTION-ONLY / EXCLUDE-OPTIONAL-EXERCISE |
| p. 396 | Qualitative dependence pattern for an analogous `Delta r` bound; no inequality, coefficients, norm choice, or remainder are printed | A precise external residual-perturbation result, if selected later | DEFER-MISSING-PRECISE-STATEMENT |
| Approximate attainability after Theorems 20.1-20.2 | Qualitative external attribution | Wedin/source-specific construction | ATTRIBUTION-ONLY |

## Open selected-scope items

None.

## Hidden-hypothesis summary

- Genuine algorithm domains such as gamma validity, no underflow, and computed
  diagonal nonbreakdown are classified as model-validity/nonbreakdown
  assumptions and shown explicitly.
- The former Theorem 20.5 full-row-rank premise was a suspicious proof artifact
  because it excluded genuinely tall full-column problems; this split removes
  it from the source-facing route.
- Theorem 20.9 existence formerly appeared only behind rank assumptions; the
  new exact Householder construction separates existence from the printed
  rank/nonsingularity equivalence.
- Theorem 20.7's local forward-row, component-operation, and multiplier-budget
  assumptions are stronger than gamma validity and diagonal nonbreakdown alone.
  They are stated as the visible domain of the corrected rounded producer, not
  claimed automatically for an arbitrary `FPModel`. The impossible exact-tail
  field is absent; `sigmaCounter_no_coxHighamRowPolicy` documents why.
- Theorem 20.10 `0 < p` and `0 < q` are implementation branch restrictions,
  not source assumptions; empty-block branches are tracked explicitly.

## Weak-component and bottleneck summary

Two independent source/type audits compared all named theorem declarations
against the PDF. The repair closes the total Theorem 20.4 perturbations, the
rounded Theorem 20.7 scale bridge, the square edge of (20.19), and Theorem
20.10's boundary branches. The MGS statement with an unspecified source
constant remains correctly deferred rather than selected. The final
verification pass repeats the focused compile, placeholder scan, axiom audit,
import coverage, and clean-diff checks.

## Verification

- Baseline direct compiles passed for `LSPerturbation.lean`, `LSQRSolve.lean`,
  `LSNormalEquations.lean`, and `LSE.lean`.
- Baseline aggregate builds passed for `LeanFpAnalysis.FP.Algorithms`,
  `LeanFpAnalysis.FP`, and the root target (3931 jobs at the audited baseline).
- `examples/LibraryLookup.lean` compiled after the public-navigation addition.
- Baseline forbidden-token, merge-marker, whitespace, import-coverage, and
  representative `#print axioms` audits passed. The representative theorems
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Final focused `LSQRSolve.lean` compilation passed with the source-general
  Theorem 20.5 package; its local forbidden-token and diff checks also passed.
- Refreshed `LSE.olean` and direct `Higham20Theorem20_10.lean` compilation
  passed after adding both source-permitted nontrivial empty-block branches.
- Direct compilation and the module-target build for
  `Higham20Theorem20_7Contract.lean` passed after the rounded-policy and
  pivot-position repair. A focused axiom audit of the Theorem 20.4 total
  endpoint, the Theorem 20.7 pivot-position endpoint, and its exact 1-by-1
  nonvacuity witness reported only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Final post-repair builds passed for `LeanFpAnalysis.FP.Algorithms` (3878
  jobs), `LeanFpAnalysis.FP` (3929 jobs), and the root target (3931 jobs).
  `examples/LibraryLookup.lean` also passed after rebuilding the aggregate
  imports and correcting the fully qualified public names.
- All 32 least-squares modules are imported by
  `LeanFpAnalysis.FP.Algorithms`. A 12-endpoint final axiom audit, covering
  every repaired proof family, reported only `propext`, `Classical.choice`,
  and `Quot.sound`. Added-line forbidden-token, conflict-marker,
  source-count, and `git diff --check` audits passed.
- These verification results validate the implemented theorem surfaces and
  support the Chapter 20 **PASS (EXPLICIT-DOMAIN)** gate.

## Documentation

- Source inventory: `docs/chapter20/CHAPTER20_SOURCE_INVENTORY.md`.
- Not-proved ledger: `docs/chapter20/CHAPTER20_NOT_PROVED_LEDGER.md`.
- Proof-source ledger: `docs/chapter20/CHAPTER20_PROOF_SOURCE_LEDGER.md`.
- Historical append-only coverage log: `docs/source_coverage/higham_ch20.md`.
- Public lookup: `docs/LIBRARY_LOOKUP.md` and `examples/LibraryLookup.lean`.
- No theorem PDF was generated; the authoritative artifacts are Lean source
  plus the decision documents above.

The local skill metadata records the corrected Chapter 20 counts: 12 named
results, 36 printed equation tags, 13 Problems, and 11 Appendix rows.
