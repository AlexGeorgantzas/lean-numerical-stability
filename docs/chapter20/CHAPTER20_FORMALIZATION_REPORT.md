# Chapter 20 Formalization Report

## Outcome

Chapter 20 now has a complete source-order audit and its source-facing modules
integrated through `LeanFpAnalysis/FP/Algorithms.lean`. All selected numbered
equations are closed or explicitly deferred, and all 12 named results pass at
their documented APIs.

The modular core selected-scope gate is **PASS**. Theorem 20.7 and Problem
20.5 now close through concrete literal-execution producers and numerical
interfaces that do not smuggle in a least-squares minimizer, returned solution,
or final Chapter 20 conclusion. Their sharper printed constants remain
source-strengthening boundaries in `CHAPTER20_NOT_PROVED_LEDGER.md`, not
missing no-placeholder producers or Chapter 20-owned selected blockers.

No `sorry`, `admit`, new global `axiom`, `unsafe` or `opaque` declaration, or
proof-disabling option was added.

## Source audit

- Primary source: Higham, *Accuracy and Stability of Numerical Algorithms*,
  2nd ed., Chapter 20, printed pp. 381-406.
- PDF SHA-256:
  `7CA85D5CAF3FFD5AE90FB315E9B4E00912E174881BCF969E7BA0A7B3CE9EC814`.
- Audited counts: 12 named results, 36 actually printed equation tags,
  13 Problems, and 11 Appendix A Chapter 20 solutions.
- `(20.13)` and `(20.15)` are group references, not additional printed tags;
  the displayed tags are `(20.13a/b)` and `(20.15a/b)`.

The authoritative inventory is `CHAPTER20_SOURCE_INVENTORY.md`; proof
provenance is in `CHAPTER20_PROOF_SOURCE_LEDGER.md`.

## Principal closures

### Perturbation theory and pseudoinverses

- `higham20_theorem20_1_solution_and_residualRelativeRHS_le_of_one_rhs_budget`
  packages both full-column Wedin conclusions.
- `higham20_alternative_theorem20_2_combined_bound` proves the p. 384 combined
  block-inverse estimate for an arbitrary absolute norm and genuine
  subordinate bound.
- `higham20_problem20_3_compactSVD_moorePenrose`,
  `higham20_problem20_3_moorePenrose_unique`, and
  `higham20_problem20_3_moorePenrose_involutive` close the arbitrary-rank
  compact-SVD construction, uniqueness, and `(A^+)^+=A`.
- `higham20_lemma20_11_equalRank_pseudoinverse_op2_le` and
  `higham20_lemma20_12_equalRank_moorePenrose` close the arbitrary-equal-rank
  Wedin lemmas.

`Higham20GeneralWedin.lean` also proves the exact Moore-Penrose difference
decomposition. Its endpoint
`higham20_general_rank_unchanged_theorem20_1_source_discrepancy` gives a fully
rational equal-rank `3`-by-`3` counterexample to the stronger p. 402 solution
bound. That source sentence is classified **PASS / SOURCE DISCREPANCY**, not as
an open theorem with altered assumptions.

### Householder QR, residual quality, and refinement

`Theorem20_3.householder_qr_fl_backSub_backward_error` ties the literal
Householder panel, transformed RHS, and `fl_backSub` result to the printed
columnwise matrix and normwise RHS backward error under visible gamma-validity
and triangular nonbreakdown guards.

`Higham20ResidualQuality.lean` proves both exact post-QR residual identities
and the sharp p. 385 Euclidean estimate. The actual-computation endpoints are:

- `Theorem20_3.householder_qr_fl_backSub_residual_quality_euclidean_sharp_finite`;
- `Theorem20_3.householder_qr_fl_backSub_conventional_residual_euclidean_sharp_finite`.

Their leading coefficient is exactly the sum of the two displayed Euclidean
norms; the source `O(u^2)` is replaced by an explicit rational small-gain
remainder. The norm hypotheses are genuine subordinate bounds for explicit
matrices, not the target residual inequality.

`higham20_eq20_16_actual_householderQR_one_refinement_finite` instantiates the
actual conventional residual, Theorem 20.4 correction solve, and rounded
update for one step of (20.16).

The p. 385 matrix-only variant is **PASS (EXPLICIT-DOMAIN)**.
`Theorem20_3_ZeroDeltaB.metricGraphSmallness_of_frobNorm_le` derives the full
metric-graph certificate from a source-sized Frobenius perturbation bound and
the two scalar Neumann guards
`rhsRadius fp m n < 1` and
`metricDefectEnvelope fp m n < 1`.
`householder_qr_fl_backSub_matrix_only_backward_error_all_rhs_of_scalar_smallness`
uses that result with the literal computed vector, handles every RHS, and
constructs only a columnwise-bounded `DeltaA`.

### Normal equations and symbolic examples

`higham20_eq20_13a_b_normal_equations_source_closed` proves the finite source
forms of (20.13a/b), and
`higham20_eq20_13a_b_fl_gram_fl_cholesky_source_closed` instantiates the actual
rounded Gram, RHS, Cholesky, and two-solve computation. The explicit gamma
remainders replace both printed `O(u^2)` terms.

`higham20CrossProductExample_fl_gram_eq` evaluates the actual rounded
cross-product example in an explicit floating-point model, and
`higham20CrossProductExample_fl_gram_singular` proves the resulting all-ones
Gram matrix singular.

The page-383 `3`-by-`2` example has a separate checked source discrepancy: the
displayed vectors imply `||r-s||_2/||b||_2 = 1/sqrt(10)`, whereas the book
prints the unnormalized value `1/sqrt(5)` as a relative value.

### Equality-constrained least squares

`Theorem20_8.source_facing_firstOrder_plus_eps_sq_of_finalSmallnessThreshold`
closes Theorem 20.8 / (20.25): it constructs a rank-tolerant `(AP)^+`, derives
both perturbed rank conditions from a source-only local threshold, and bounds
the actual relative minimizer displacement by the exact printed first-order
coefficient plus an explicit quadratic term.

`higham20_eq20_26_canonical_weighted_branch_tendsto_unique_lse` and
`higham20_eq20_26_exists_weighted_minimizer_branch_tendsto_unique_lse`
construct the weighted minimizer branch and prove its convergence to the
unique LSE minimizer.

`Higham20EliminationActual.lean` constructs the p. 399 wide active-max
signed-Householder QR of `B`. It proves `R1` nonsingular from source full row
rank, performs the exact backsolve, and closes the algorithm with
`lseEliminationActual_isLSEMinimizer_of_reduced_minimizer`. The only final
algorithm input is correctness of the explicitly requested reduced
unconstrained least-squares subsolve.

### MGS transfer and Theorem 20.7 modular boundaries

`Higham19Alg12MGSRounded.lean` defines the literal rounded Algorithm 19.12
loop. `fl_modifiedGramSchmidt_roundedState` proves its diagonal norm,
normalization, strict-upper dot-product, later-column update, and
upper-triangular fields. The same module now telescopes those local errors into
`mgsRoundedProductEntryBudget`, proves the polar-resolvent correction bound,
and constructs `ModifiedGramSchmidtGlobalRepair` with
`toGlobalRepairWithAccumulatedPolarBudget`. `Higham19Alg12MGSRepair.lean`
adds `toGlobalRepairWithLocalGramBudget`: from the directly computed runtime
premise `||I-QhatᵀQhat||_F <= gramCoeff*u`, its explicit numerator is the
local trace budget plus `gramCoeff*u*||Rhat(:,j)||₂`, never the realized
repair residual.

`Problem20_5.actualAugmentedMGSBackSub_end_to_end_accumulatedPolar` and
`actualAugmentedMGSBackSub_end_to_end_localGram` then fix the actual `[A b]`
factors, run literal `fl_backSub`, and construct the nearby exact minimizer.
This gives **PASS (LITERAL END-TO-END ACCUMULATED-POLAR; COMPUTED-GRAM
EXPLICIT-DOMAIN)**. The accumulated-polar theorem has no external repair
premise on its explicit tall/full-pivot/positive-column and gamma-valid domain;
the local-Gram variant instead exposes the computed Gram-defect inequality.
The polar coefficient can depend on computed Gram defect and
`Rhat`/source-column ratios; it is not claimed to be Higham Theorem 19.13's
stronger condition-number-independent printed `c3*u` bound. That
padded-Householder/QR-sensitivity strengthening remains upstream.

For Theorem 20.7, `PivotedStoredQRSplit3BNumericalContract` exposes exactly
the matrix-residual, RHS-residual, and back-substitution-transport bounds for
the literal traces. It contains no minimizer, returned-vector, or final
backward-error field.
`Theorem20_7.fl_pivotedStoredQR_returnedX_exactMinimizer_of_split3B` consumes
that numerical contract, runs the literal rounded backsolve assembly, and
proves the exact minimizer and source-row perturbation bounds. Together with
the runtime producer below, this is **PASS (CH20 ASSEMBLY / LITERAL RUNTIME
PRODUCER; EXPLICIT-DOMAIN;
SOURCE-COORDINATE CORRECTION)**.

`Higham20Theorem20_7QdR.lean` directly supports the numerical interface: it
proves the Cox--Higham (3.7) reflector-prefix expansion, the prefix-policy
`Q[DeltaR;0]` bound, and a two-scale transport lemma that keeps the raw
reflector's forward `alpha` scale separate from an RHS residual's `beta`
scale. `pivotedStoredQR_QdR_source_n_sq_le_of_prefixReady` supplies the
transported correction row bound with `backSubCoeff = 16 * eta`; no strict
cross-stage sigma-history premise is used.

`Higham20Theorem20_7Contract.lean` now contains the conditional printed
Cox--Higham producer. `pivotedStoredQR_split3B_numericalContract_of_coxHigham`
derives the three literal-trace contract fields from explicit forward
row-policy and primitive local component-budget hypotheses, with coefficients
`5*gammaTilde`, `5*gammaTilde`, and `16*gamma_n`.
`fl_pivotedStoredQR_returnedX_exactMinimizer_of_coxHigham` immediately feeds
that constructor to the actual `fl_backSub` consumer. The rowwise core uses
the exact forward `alpha`/`beta` numerators; the separate
`PivotedStoredQRCoxHighamRowSortingCaps` is used only by the optional
initial-row-scale corollary. A common row-permutation wrapper is also proved
with inverse-permutation source transport.

Two formal obstructions prevent stronger but false packaging.
`sigmaHistory_not_forall_literal_rounded_trace` refutes the legacy strict
cross-stage sigma history for a literal rounded trace, and
`pivotPositionFactor_not_le_sourceColumnFactor_forall` refutes relabeling the
sharp pivot-position `j^2` factor by an original source-column index. The
corrected endpoints keep `j^2` in pivot-position coordinates and use the
proved uniform `n^2` factor in source coordinates. The printed producer is
honestly conditional: the literal trace performs column pivoting but no row
sorting, and `localBudgetReady_not_forall_printed_source_row_scale` gives an
exact-arithmetic counterexample to a universal same-row initial-scale
instantiation. `Higham20Theorem20_7Runtime.lean` supplies the separate
conservative closure: `pivotedStoredQR_split3B_numericalContract_runtime`
constructs the contract from finite execution-derived matrix/RHS stage sums
and a generic final top-`R` transport scale, with no row-policy or
component-budget premise, and
`fl_pivotedStoredQR_returnedX_exactMinimizer_of_runtime` feeds it to the actual
`fl_backSub` endpoint. This conservative row-uniform, execution-derived
exact-Real runtime certificate closes the literal computation on the visible
`n > 0`, gamma-valid, nonzero-top-diagonal domain. It is not a Lean-executability
claim and must not be confused with the sharper printed Cox--Higham
source-row compression.

## Named-result status

| Result | Status |
|---|---|
| Theorem 20.1 | PASS at the full-column source API |
| Theorem 20.2 | PASS |
| Theorem 20.3 | PASS (EXPLICIT-DOMAIN) |
| Theorem 20.4 | PASS (EXPLICIT-DOMAIN) |
| Theorem 20.5 | PASS at the finite-positive/eigenvalue/matrix-only APIs |
| Lemma 20.6 | PASS |
| Theorem 20.7 | PASS (CH20 ASSEMBLY / LITERAL RUNTIME PRODUCER; EXPLICIT-DOMAIN; SOURCE-COORDINATE CORRECTION) |
| Theorem 20.8 | PASS (EXPLICIT-DOMAIN) |
| Theorem 20.9 | PASS |
| Theorem 20.10 | PASS (EXPLICIT-DOMAIN) |
| Lemma 20.11 | PASS at the arbitrary-equal-rank MP API |
| Lemma 20.12 | PASS at the arbitrary-equal-rank MP API |

## Trust and assumption audit

- Theorem 20.8, the sharp residual theorem, normal-equation/refinement
  closures, weighted limit, alternative bound, Problem 20.3, the elimination
  method, and both source-discrepancy counterexamples have no target-equivalent
  hypotheses.
- The remaining upstream/source-strengthening rows concern only the sharper
  printed `c3*u` or Cox--Higham row-local constants. The literal MGS and QR
  producers are connected, and none of their interfaces contains a Chapter 20
  minimizer, returned-vector, or final theorem conclusion.
- External citations and unsuccessful Oracle consultations were not used as
  proof terms.
- Representative public endpoints depend only on `propext`,
  `Classical.choice`, and `Quot.sound`.

## Repository integration and verification

The aggregate imports all 28 Chapter 20 modules, including the Split 3B
contract, Cox--Higham support, and runtime producer modules. Both literal MGS
modules are imported with their Chapter 20 consumer. The final focused
six-module MGS/Theorem 20.7 build passed all 3087 jobs; the aggregate
`LeanFpAnalysis.FP.Algorithms` build passed all 3878 jobs; and the full
repository build passed all 3931 jobs. Nine representative endpoint
`#print axioms` checks each reported exactly `propext`, `Classical.choice`, and
`Quot.sound`. The forbidden-declaration scan, aggregate-import coverage, and
`git diff --check` also passed.

Pre-existing Chapter 14 working-tree edits were not modified by this Chapter
20 work.

## Skill and planning metadata

The local Chapter-splitting skill, its mirror, the blueprint, primary-contract
matrix, and chapter index already carry the corrected Chapter 20 ownership and
counts: 12 named results, 36 printed equation tags, Problems 20.1-20.13, and
Appendix solutions 20.1-20.11. No additional skill-policy edit was necessary;
proof progress and upstream source-strengthening boundaries belong in the
chapter ledgers above.
