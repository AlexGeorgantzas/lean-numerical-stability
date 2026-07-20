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
- Selected-scope gate: **PASS**.

Most implementation-facing theorems expose legitimate model-validity and
nonbreakdown domains. Theorem 20.7 is terminal at an actual-trace endpoint whose
only extra algorithm-domain premise is nonzero computed diagonal; no numerical
policy, budget, residual, readiness, or target-bound certificate is assumed.

## Split 4 repair outcome

The 2026-07-16 pass re-read all chapter and Appendix pages and corrected prior
overclaims. The fresh 2026-07-19 actual-trace repair then closed the remaining
Theorem 20.7 producer. The resulting source-strength improvements are:

| Source label | Lean declaration | File | Theorem surface | Status |
|---|---|---|---|---|
| Theorem 20.5 / (20.20)-(20.21) | `theorem20_5_wks_finite_formula_and_eigenvalue`, `theorem20_5_wks_formula_eigenvalue_and_matrixOnly_limit` | `LSQRSolve.lean` | Arbitrary printed-shape least-squares data, `y != 0`, finite positive `theta`, minimizer/nonminimizer branches, and matrix-only limit | PASS |
| Theorem 20.4 total-perturbation surface | `LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_householderQRPanel_theorem20_4_printed_total_perturbations` | `Higham20Theorem20_4Absorption.lean` | Packages both actual `DeltaA_i`, the exact augmented system, one shared nonnegative Frobenius-unit witness, and the printed componentwise envelopes with an explicit dimension-only `lsTheorem20_4ConcreteGammaTildeTotal` | PASS (EXPLICIT-DOMAIN) |
| Equation (20.16) | `higham20_eq20_16_augmented_one_refinement_finite`, `higham20_eq20_16_augmented_one_refinement_actual_residual_update`, `higham20_eq20_16_actual_householderQR_one_refinement_finite` | `Higham20Equations.lean`, `Higham20Refinement.lean` | Proves the source residual chain, expands the gamma factors into the printed first-order terms plus an exact rational quadratic-and-higher remainder, instantiates the actual residual/update kernels, and separately connects the literal QR correction path to its implementation majorant | PASS; the formerly separate Theorem 20.4 upstream row is also closed |
| Theorem 20.9 / (20.27)-(20.28) | `GeneralizedQRFactorization.exists_theorem20_9_exact_householder` | `LSE.lean` | Unconditional GQR existence under the printed dimension inequalities; rank assumptions are separate | PASS |
| Cross-product example | `higham20CrossProductExample_symbolic_family` | `Higham20CrossProductExample.lean` | Symbolic `0 < epsilon < sqrt(u)` family, actual modeled rounded Gram, all-ones identity, singularity | PASS |
| p. 383 projector-complement identity | `higham20_fullColumn_range_projector_complement_complexMatrixOp2_eq_min_one_sub` | `Higham20Prose.lean` | Exact `||I-AA^+||_2 = min {1,m-n}` including square/tall cases | PASS |
| Theorem 20.7 actual rounded endpoint | `higham20_7_sourceConstructed_actual_closed` | `Higham20Theorem20_7ActualBackSub.lean` | Executes the literal rounded pivoted stored-QR, paired RHS transformation, and `fl_backSub`; constructs the triangular-solve perturbation and exact perturbed minimizer; derives the matrix/RHS budgets and `Q Delta R` transport; and proves both printed uniform source-order `n^2` envelopes with one explicit coefficient depending only on `fp,m`. No policy or target-bearing certificate is assumed. | PASS (EXPLICIT-DOMAIN) under gamma validity, the visible half-gamma guard, and nonzero computed diagonal |
| p. 395 row-sorting cap and `phi` invariance | `Higham20RowSorting.exactPrinted_iSup_max_alpha_beta_le_cap_of_source_injective`, `exactPrintedPhi_eq_qrCertificate`, `exactPrintedPhi_independent_of_row_ordering` | `Higham20RowSorting.lean` | Executes decreasing source-row infinity-norm sorting, derives positive exact pivots from ordinary source full column rank, proves the literal finite `max_i` cap for the paired exact active-max trace, identifies the stagewise `phi` with the terminal QR certificate, and proves simultaneous-row-permutation invariance. | PASS (EXPLICIT-DOMAIN) |
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
| Theorem 20.7 | PASS (EXPLICIT-DOMAIN) | `higham20_7_sourceConstructed_actual_closed` derives the raw/prefix growth, matrix/RHS operation budgets, direct `Q Delta R` estimate, permutation transport, exact minimizer, and printed uniform source-order bounds from the actual trace. Its common `sourceConstructedPivotedStoredQRFinalGammaTilde fp m` is data independent. Full source rank and bare gamma validity still cannot imply computed nonbreakdown, so nonzero computed diagonal is exposed honestly. |
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
| Corrected Cox-Higham rounded-feedback analysis | Theorem 20.7's printed row-local constants must come from an execution whose stage invariants account for rounded feedback | Actual forward-row/prefix bounds, compact-operation budgets, triangular-column transport, `Q Delta R` pullback, and exact minimizer assembly | Implemented and compiled in `Higham20Theorem20_7ActualBackSub.lean`. Source rank/gamma alone cannot produce pivot nonbreakdown (`breakdownCounter_no_roundedRowPolicy`), so nonzero computed diagonal remains explicit. |
| Row-sorting growth producer and `phi` invariance | The precise sentence after Theorem 20.7 requires an actual row policy, the common `sqrt(m)(1+sqrt(2))^(n-1)` cap, and invariance of `phi` | `Higham20RowSorting.lean` exact sorted matrix/RHS trace, Cox--Higham stage growth, source-rank-derived nonbreakdown, completed QR certificate, and simultaneous-row-permutation transport | Implemented and compiled under ordinary source full column rank |
| Total Theorem 20.4 perturbation absorption | The printed named theorem requires single-witness bounds for both total `DeltaA_i` | Theorem 20.4 | Implemented by transporting each triangular correction through the exact QR relation, summing the two nonnegative witnesses, and normalizing once |

## External proof sources

| Selected claim | Source and location | Role | Local Lean closure | Status |
|---|---|---|---|---|
| Theorem 20.1 | Wedin citation summarized in pp. 400-402 | Perturbation route and attainability attribution | Full-column inequalities local; stronger p. 402 sentence refuted by exact counterexample | ADOPTED/REJECTED AS CLASSIFIED |
| Lemma 20.12 | Stewart and Stewart-Sun citations on p. 400 | Cross-projection norm equality | Proved locally at arbitrary equal rank | ADOPTED |
| Theorem 20.5 | Walden-Karlson-Sun citation, pp. 392-393 | Backward-error/eigenvalue formula | Proved locally after source-generality repair | ADOPTED |
| Theorem 20.7 and following row-sorting prose | Powell-Reid/Cox-Higham citation, p. 395 | Printed row-local producer followed by the common row-sorting cap and `phi` invariance | The rounded theorem is proved from the literal actual trace in `Higham20Theorem20_7ActualBackSub.lean`; the following precise prose is proved independently for the executable exact row-sorted trace | ADOPTED AND PROVED (EXPLICIT-DOMAIN); FOLLOW-ON PROSE PROVED |
| Theorem 20.8 | Elden/Cox-Higham citation, p. 396 | First-order LSE perturbation route | Proved locally on explicit source-only threshold | ADOPTED |
| Theorem 20.10 | Cox-Higham citation, pp. 398-399 | Rounded GQR stability | Positive-block path and both nontrivial empty-block boundary branches are proved locally on explicit source-rank/roundoff domains | ADOPTED |
| Difficult Theorem 20.7 audit | Oracle second-model consultation, slug `chapter20-theorem20-7-audit` | Independent source/type review and dependency-plan check | Its rejection of the earlier weaker endpoint and its pivot-position/rounded-feedback dependency outline were checked against the PDF and Lean types. The required concrete actual-trace producer is now implemented locally; the model supplied no trusted proof object. | ADVISORY; VERIFIED DIAGNOSIS/PLAN ADOPTED AND LOCALLY COMPLETED |

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
- Theorem 20.7's historical local forward-row, component-operation, and
  multiplier-budget contract is not accepted as closure evidence. The new
  actual-trace theorem derives those numerical estimates and the final
  perturbations directly. The full-rank gamma-valid
  `breakdownCounter_no_roundedRowPolicy` still shows that source rank alone
  cannot produce computed nonbreakdown; the final endpoint therefore exposes
  nonzero computed diagonal as an honest algorithm-domain premise.
- The separate `PivotedStoredQRCoxHighamRowSortingCaps` fields remain
  target-bearing and are not counted as evidence. The p. 395 prose row is
  instead closed by the independent executable producer in
  `Higham20RowSorting.lean`; ordinary source full column rank is used to derive
  the positive exact pivots required by the printed ratios.
- Theorem 20.10 `0 < p` and `0 < q` are implementation branch restrictions,
  not source assumptions; empty-block branches are tracked explicitly.

## Weak-component and bottleneck summary

Two independent source/type audits compared theorem declarations against the
PDF. The repair closes the total Theorem 20.4 perturbations, Theorem 20.7's
actual rounded execution, the p. 395 sorting-cap/`phi`-invariance row, the
square edge of (20.19), and Theorem 20.10's boundary branches. No selected
named-result bottleneck remains. The MGS statement with an unspecified source
constant remains correctly deferred.

## Verification

- Baseline direct compiles passed for `LSPerturbation.lean`, `LSQRSolve.lean`,
  `LSNormalEquations.lean`, and `LSE.lean`.
- Baseline aggregate builds passed for `NumStability.Algorithms`,
  `NumStability`, and the root target (3931 jobs at the audited baseline).
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
- The fresh 2026-07-18 bounded Theorem 20.7 repair also passed direct
  compilation and the focused module-target build (3082 jobs). Axiom checks
  for `PivotedStoredQRCoxHighamForwardRowPolicy.of_trace_core`, both rounded
  envelope constructors, `breakdownCounterA_mulVec_injective`, and
  `breakdownCounter_no_roundedRowPolicy` reported only `propext`,
  `Classical.choice`, and `Quot.sound`; placeholder, conflict-marker, and diff
  checks passed.
- The 2026-07-19 `Higham20Theorem20_7ActualBackSub.lean` repair passed focused
  direct compilation. Its source-facing endpoint is
  `higham20_7_sourceConstructed_actual_closed`; the new module is imported by
  `NumStability.Algorithms`. A fresh aggregate/root build is left to the
  final integration pass rather than inferred from the earlier baseline.
- Final post-repair builds passed for `NumStability.Algorithms` (3878
  jobs), `NumStability` (3929 jobs), and the root target (3931 jobs).
  `examples/LibraryLookup.lean` also passed after rebuilding the aggregate
  imports and correcting the fully qualified public names.
- All 32 least-squares modules are imported by
  `NumStability.Algorithms`. A 12-endpoint final axiom audit, covering
  every repaired proof family, reported only `propext`, `Classical.choice`,
  and `Quot.sound`. Added-line forbidden-token, conflict-marker,
  source-count, and `git diff --check` audits passed.
- The older target-bearing row-sorting and rounded-policy contracts are not
  used for closure. The independent exact row-sorting producer closes the
  separate p. 395 prose row, while the new actual rounded producer closes the
  named theorem without policy or target-bound premises. The Chapter 20 gate
  is **PASS**.

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
