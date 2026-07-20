# Higham Chapters 1--28 -- independent PDF-first rerun (2026-07-19)

## Result

**28 PASS, 0 FAIL, 0 BLOCKED.**  Every core-mode source row and every
exact-label inter-chapter composition gate is terminal under the rules below.

This is the authoritative rerun requested against remote `main`.  It was
performed independently of the conclusions in the coverage ledgers and the
earlier 2026-07-19 report.  The PDFs were the source of truth; ledgers were
consulted only after the source inventory and declaration-type audit.

## Frozen baseline and source corpus

- Repository: `https://github.com/AlexGeorgantzas/lean-fp-analysis.git`
- Audited branch: `origin/main`
- Frozen baseline commit: `78cda8ba9debad7af00d2dd6a1b01f096551a488`
- Local branch at freeze: `main`, exactly equal to `origin/main`
- PDFs: `References/1.9780898718027.ch1.pdf` through
  `References/1.9780898718027.ch28.pdf`
- Corpus size: 28 files, 7,102,905 bytes, 513 PDF pages
- SHA-256 of the 28 raw PDF byte streams concatenated in numeric chapter
  order: `ad45eea4a5b197728cd00653a32d0b61bc009a2c35898d7dbe7e00f0ca7f362b`

The baseline itself passed a clean full `lake build` of 4,405 jobs before any
repair was used as evidence.

## From-scratch inventory

The rerun extracted every chapter afresh and rendered source pages whenever
formula layout, a domain, a matrix block, or a proof handoff could not be
trusted to text extraction.  It found 165 distinct typed named headings in the
chapter bodies:

| Chapters | Named headings per chapter |
|---|---|
| 1--7 | 1, 5, 9, 3, 2, 5, 9 |
| 8--14 | 14, 15, 14, 9, 4, 10, 7 |
| 15--21 | 9, 0, 0, 2, 13, 12, 4 |
| 22--28 | 8, 4, 3, 2, 0, 0, 1 |

This count corrects the previous Chapter 9 inventory.  Chapter 9 has 15 named
items--Algorithm 9.2, Lemma 9.6, and Theorems 9.1, 9.3--9.5, 9.7--9.15--not
14.  Theorem 9.7 was missing from the earlier summary.

There are 597 distinct current-chapter numbered equation labels.  Twelve occur
only in optional Problems: (6.23)--(6.24), (8.21), (13.26), (14.37),
(19.38)--(19.40), (21.12)--(21.14), and (25.15).  Excluding those optional
exercise rows leaves 585 body-equation labels.  Every body label was checked
in its PDF context; a literal numeral in a Lean name was navigation evidence,
not proof of closure.

## Gate applied

The repository skill's core-mode rules were applied literally:

- each precise selected theorem, lemma, algorithm, body equation, and central
  mathematical prose claim needs a compiled source-strength endpoint;
- an implementation-facing theorem must begin with the actual rounded
  executor, not a caller-supplied residual, execution, growth, or target
  certificate;
- a hypothesis equivalent to the desired conclusion cannot close a row;
- mathematical domains and hidden nonbreakdown/smallness conditions must be
  explicit;
- undefined approximation signs, unquantified `O(.)`, unspecified algorithms,
  empirical observations, and adjectives such as “modest” or “small” are
  `DEFER-MISSING-PRECISE-STATEMENT`, not invitations to invent a theorem; and
- a false source row is terminal only with a compiled counterexample and a
  faithful corrected theorem.

Problems remain outside core mode unless a selected result consumes one.

## Defects found and repairs made

The frozen remote baseline was not closed under that gate.  The rerun found
the following defects that the previous `28 PASS` report missed.

### Chapters 2 and 3

The PDF explicitly says that (3.3)--(3.5) remain valid under the no-guard
rounding model (2.6). `HighamChapter3NoGuardDotBridge.lean` now supplies an
actual no-guard dot executor, tracks the separate accumulator/input
perturbations of every addition, proves the exact local-factor expansion and
`gamma_n` backward/forward endpoints, and covers every binary association and
input permutation through an actual `SumTree.noGuardEval`. The standard-model
dot theorem is no longer used as a semantic substitute for this claim.  The
rerun also corrected the foundational no-guard witness domain from strict
`< u` to the PDF's literal boundary-inclusive `≤ u`; all existing no-guard
consumers were rebuilt under that wider model.

### Chapters 7 and 15

Chapter 15 equation (15.1) is the norm identity for the nonnegative practical
error-budget vector introduced by (7.31), not the 1-norm condition-number
definition previously listed in the Chapter 15 ledger. The corrected bridge
proves nonnegativity of the actual computed-residual safety vector and composes
the real (7.31) endpoint with `cond_norm_identity`.

### Chapter 9

- **Equation (9.14) stopped at the exposed upper factor rather than the
  source definition's maximum over every reduced matrix.**
  `HighamChapter9CompletePivotSharpClosure.lean` now starts from the actual
  recursive GECP trace, defines the history set from the original matrix and
  every recursively produced Schur stage, and proves its supremum growth
  factor is bounded by Wilkinson's exact product. The endpoint has no
  caller-supplied pivot sequence, stage bound, or growth certificate.
- **Theorem 9.7 was absent from the summary and lacked the literal
  classification.**  `HighamChapter9Theorem97Classification.lean` constructs
  the exact leading-row-on-ties GEPP trace for every nonsingular real matrix.
  Equality in the source reduced-matrix growth history, not merely final `U`,
  forces no row interchanges and the printed
  `A = D M [T | alpha d; 0 | alpha*2^(n-1)]` classification.  The `n=1` case is
  included.
- **Theorems 9.8--9.11 were printed over complex matrices, while prominent
  endpoints were real specializations.**  The new complex closure proves the
  universal arbitrary-`P,Q` Theorem 9.8, constructs actual complex GEPP traces
  for upper Hessenberg and banded matrices, proves the Bohte bound, the PDF's
  displayed `n=9=2*4+1` near-attainability witness, and the tridiagonal bound
  `rho <= 2`.  The more general adjective “almost attainable” has no stated
  tolerance and is not silently promoted to a quantified theorem.
- **Theorem 9.9 did not expose its complete no-pivot reduced history.**  The
  new real and complex closures construct exact no-pivot LU for nonsingular
  row/column diagonally dominant matrices, prove the full (9.5) reduced-stage
  growth bound `rho <= 2`, and prove the column-dominant multiplier bound.

### Chapter 11

The last paragraph of section 11.1.1 uses the Chapter 9 bound (9.14) in
Bunch's sharper `3.07 (n-1)^0.446` comparison. The old bridge merely defined
that multiplier. The replacement keeps one-by-one and two-by-two pivots
atomic, proves the weighted logarithmic argument at genuine block boundaries,
and records the unavoidable order-one source discrepancy: the printed
multiplier is zero at `n=1`. Its implementation-facing adapter extracts pivot
determinant lower bounds and adjacent-stage growth from the exact complete-
search/symmetric-permutation/Schur trace of Algorithm 11.1. The strict route
now starts one level earlier: every symmetric nonsingular source constructs
such an exact trace by finite entry/diagonal maxima and determinant-preserving
Schur recursion. Every nonempty trace prefix is realized as a selected
principal minor of its active source matrix, whose determinant is exactly the
product of its atomic pivot-block determinants. The complete-search entry
bound and Hadamard's inequality then derive the required estimate for every
contiguous whole-block segment. Consequently
`higham11_1_exists_exactBunchTrace_all_stageRatio_le_maxEntryNorm` proves the
all-stage sharp ratio bound from the source domain itself, with no caller-
supplied trace, determinant identity, Hadamard fact, growth certificate, or
target bound.

Separately, displayed equation (11.7) now starts from the actual mixed
block-LDLT executor and actual rounded outer triangular solves. It derives
both the componentwise first-order line and the condition-product line using
the Chapter 9 (9.23) handoff, with the sanctioned local (11.5) two-by-two
middle-solve certificate as its only solve-side input.

The PDF prints Theorem 11.8 without `n >= 2`, but its stated radius is zero at
`n=1`.  The actual coupled `flAasen`/rounded-division execution refutes the
unrestricted statement, and `higham11_8_n_one_sharp_corrected_bound` proves the
forced sharp scalar correction.  This is terminal `SOURCE-DISCREPANCY`; it is
not a claim that a corrected all-orders theorem for `n >= 2` has been proved.

### Chapter 14

The existing operational bridge stopped before Algorithm 14.4's final
componentwise divisions.  `Ch14GJEFinalDivisionClosure.lean` analyzes the
actual `fl_div` output, carries the new error through general-diagonal
(14.29)--(14.30), and derives the actual-output (14.31)--(14.32), Theorem 14.5,
and the Corollary 14.6/14.7 vanishing-family adapters with explicit named
higher-order terms. In Corollary 14.6 the printed leading residual term uses
the exact solution norm `‖x‖₂`; the difference from the actual output norm is
now included in a named remainder and proved `O(u²)` from the actual output's
proved `O(u)` forward error. Corollary 14.7 has its own actual-run family and
ratio-free bootstrap rather than inheriting a fixed-run asymptotic claim.

The first phase is no longer an abstract supplied LU certificate:
`Ch14GJEActualDoolittleAdapter.lean` instantiates it with the literal rounded
Algorithm 9.2 Doolittle loop and actual forward substitution. For Corollary
14.6, convergence of the derived perturbed matrices to the fixed nonsingular
source now supplies the required uniform inverse control by continuity of
matrix inversion. For Corollary 14.7, row diagonal dominance and
nonsingularity construct the exact no-pivot LU factors and upper-factor
inverse through Theorem 9.9, so callers do not supply hidden exact-analysis
objects.

### Chapter 16

The precise post-factor part of (16.9) is closed by the actual rounded RHS
transform, quasi-triangular block solve, and reconstruction from supplied exact
real-Schur factors.  The preceding rounded QR/real-Schur producer remains
`DEFER-MISSING-PRECISE-STATEMENT`: the PDF specifies no QR iteration, shift or
deflation policy, and calls the unknown constant only “modest”.  Treating that
source omission as a missing Lean bridge would require inventing an algorithm
and bound forbidden by the skill.

### Chapters 19 and 12

- `H19_Theorem19_5_qr_solve_columnwise_backward_error` was normwise despite
  its name.  `Higham19Theorem5SourceClosure.lean` now starts from
  `fl_householderQR_solve` and constructs a perturbation bounded separately in
  every column, plus a right-hand-side perturbation.  A direct Euclidean
  recursion for the actual zero-aware reflector sequence yields
  `gamma fp (n * K_n)`, with `K_n = 3*(11*n+23)`.  Its gamma index is therefore
  explicitly `O(n^2)`, matching the PDF's `tilde-gamma_(n^2)` rate without
  inventing a sharp hidden constant.
- The same module proves the unperturbed-RHS form (19.14).  For nonzero `b`,
  the bounded invertibility of `(Q+DeltaQ)^T` used silently in the PDF proof is
  an explicit domain; the zero-`b` case needs no inverse assumption.
- The Chapter 6 Lemma 6.6 bridge is now direct and yields the exact
  componentwise residual formula used in Section 19.7.  The following
  Theorem 12.4 prose uses undefined `approximately` and “small” relations and
  is deferred rather than strengthened.
- `Higham19WYApplicationClosure.lean` proves the exact WY initialization and
  recurrence (19.17), the partition/update (19.18), and the application error
  equation (19.22).  The latter constructs its perturbation and derives the
  printed `1+d1+d2*d3*(1+cInner+cOuter)` coefficient from two operator-2-norm
  instances of Chapter 13 (13.4) plus the rounded addition contract.  The
  “modest” construction constants in (19.19)--(19.21) remain explicit named
  prerequisites because the PDF specifies neither their functions nor a
  rounded construction algorithm; no target-shaped (19.22) premise is used.

### Chapters 12 and 9

The Chapter 12 solver weight (12.6) is now connected to the literal Chapter 9
rounded Doolittle factors and the actual `fl_forwardSub`/`fl_backSub`
executors. The bridge derives
`W = 3n/(1-3nu) |L_hat||U_hat|`, rewrites Theorem 9.4's constructed
`gamma_(3n)` perturbation as `uW`, and returns the exact finite Chapter 12
solver predicate. It assumes only pivot nonbreakdown and the printed gamma
domains--not a residual, execution, backward-error, or solver-bound
conclusion.

### Chapter 22 and Chapter 12

The previous refinement path was circular: the useful conclusion was already
present in a contraction-style premise.  The repaired bridge identifies the
actual rounded Horner residual with a standard-Vandermonde row and passes it
directly to the exact finite Theorem 12.3 bound. Reading the page-428 claim
literally with (12.9)'s conventional `gamma_(n+1)` coefficient is false in the
abstract standard model: a compiled `n=4`, first-derivative counterexample
uses the actual differentiated-Horner and final-subtraction operations. The
faithful correction proves the exact generated-budget (12.8) certificate for
every derivative order, over both the real and printed complex confluent
domains, then composes the correction solve and rounded update to finite
(12.10). The old contraction theorem remains only as an explicitly
conditional corollary.

## Per-chapter disposition

| Ch. | Gate | Rerun note |
|---:|---|---|
| 1 | PASS | Precise arithmetic/model rows rechecked from PDF. |
| 2 | PASS after domain repair | The no-guard (2.6) surface now uses the literal `≤ u` domain; format and standard-model rows rechecked. |
| 3 | PASS after bridge repair | Model-(2.6) no-guard (3.3)--(3.5), including arbitrary order, now has an actual executor path. |
| 4 | PASS | Literal summation executors and selected error bounds present. |
| 5 | PASS | Horner/derivative producers, including the repaired Chapter 22 consumer. |
| 6 | PASS | Norm results and Lemma 6.6 have direct Chapter 10/14/19/27/28 consumers. |
| 7 | PASS / SOURCE-DISCREPANCY | Precise perturbation rows closed; false same-`p` scaling wording retained with correction. |
| 8 | PASS / SOURCE-DISCREPANCY | Triangular solves/inverses closed; printed inequality/initialization defects retained. |
| 9 | PASS after repair | 15 named rows; actual all-reduced-stage (9.14), Theorem 9.7, and complex 9.8--9.11 now source-domain complete. |
| 10 | PASS / SOURCE-DISCREPANCY | Pivoted/complex Cholesky and domain corrections rechecked. |
| 11 | PASS / SOURCE-DISCREPANCY | Actual (11.7); source-constructed Algorithm 11.1 trace, selected-minor determinant recurrence, derived whole-block Hadamard, and unconditional all-stage sharp comparison; plus Theorem 11.8's actual `n=1` refutation/correction. |
| 12 | PASS after bridge repair | Actual Chapter 9 LU solve feeds the exact finite solver/refinement results; undefined asymptotic relations are not invented. |
| 13 | PASS | Block-LU rows and consumers rechecked. |
| 14 | PASS after repair / SOURCE-DISCREPANCY | Literal final divisions now feed 14.29--14.32 and source corollaries. |
| 15 | PASS after bridge repair / SOURCE-DISCREPANCY | Actual (7.31) safety vector now feeds correctly identified (15.1); general-`p` calculus and normalized-dual correction rechecked. |
| 16 | PASS with explicit deferral | Rounded supplied-factor suffix closed; unspecified Schur producer deferred. |
| 17 | PASS | No named headings; all selected precise body equations accounted. |
| 18 | PASS | Two named results and precise body rows accounted. |
| 19 | PASS after repair | Actual columnwise 19.5, honest 19.14 domain, direct 6.6 residual bridge, and the determinate WY (19.17)--(19.22) Chapter 13 handoff. |
| 20 | PASS / SOURCE-DISCREPANCY | Actual pivoted QR/least-squares consumer and rank-domain correction rechecked. |
| 21 | PASS / SOURCE-DISCREPANCY | Underdetermined consumers and `inf` correction rechecked. |
| 22 | PASS after bridge repair / SOURCE-DISCREPANCY | Literal (12.9) coefficient refuted; corrected actual real/complex Horner residual feeds finite Theorem 12.3 without circular contraction. |
| 23 | PASS | Fast-multiplication rows and error consumers rechecked. |
| 24 | PASS | FFT/circulant rows and earlier-chapter dependencies rechecked. |
| 25 | PASS / SOURCE-DISCREPANCY | Newton/bordered eigenproblem rows and domains rechecked. |
| 26 | PASS / SOURCE-DISCREPANCY | Precise symbolic rows closed; zero Cardano branch corrected; experiment remains empirical. |
| 27 | PASS / SOURCE-DISCREPANCY | Sticky flags/underflow/precision semantics and Smith correction rechecked. |
| 28 | PASS / SOURCE-DISCREPANCY | Precise test-matrix rows closed; false/qualitative normality claims classified. |

## Cross-chapter bridge audit

The first draft of this rerun mixed exact body-label references with references
to earlier Problems and qualitative prose. A second independent projection
corrected that accounting. There are **60 producer-to-consumer chapter pairs**
formed by exact earlier numbered/named labels in the current chapter bodies:

```text
2->3  2->4  2->5  3->5  6->7  2->8  3->8  7->8  3->9  7->9  8->9
3->10 6->10 7->10 8->10 9->10
9->11
3->12 7->12 9->12
9->13 10->13
3->14 6->14 7->14 8->14 9->14
6->15 7->15 8->15 9->15
7->16 8->16 15->16
7->17
3->19 6->19 8->19 12->19 13->19
7->20 10->20 12->20 19->20
7->21 19->21 20->21
2->22 3->22 5->22 12->22
3->23
3->24
7->25
9->26 15->26
2->27 15->27
8->28 15->28
```

This stricter pass found five genuine composition gaps in that graph:

- 2->3: the PDF says (3.3)--(3.5) remain valid under the no-guard model
  (2.6), but only the standard-model dot-product path existed;
- 7->15: the generic norm identity existed under the wrong chapter label, but
  the actual computed-residual vector from (7.31) was not composed with (15.1);
- 9->11: neither the exact Bunch `3.07 (n-1)^0.446` comparison with (9.14) nor
  the displayed (11.7) use of (9.23) had a source-shaped endpoint; the repaired
  sharp route now constructs its exact trace from a symmetric nonsingular
  source and derives its principal-minor/Hadamard obligations internally; and
- 9->12: the Chapter 12 forward-error claim cited the Chapter 9 rounded LU
  solve analysis, but no theorem composed an actual rounded LU executor with
  the actual forward/back substitution executors and the exact finite (12.2)
  bound; and
- 13->19: the level-3 block-Householder/WY path through (19.17)--(19.22),
  including its invocation of the matrix-product assumption (13.4), was absent.

The final tree repairs all five rather than treating semantic proximity as a
bridge. The previously identified 12->22 and 6/12->19 defects are also
repaired by the finite Horner/refinement and actual QR-solve/residual modules
described above. The remaining exact-label pairs have a direct compiled
handoff or a checked exact specialization; fixed numerical-table references
are not misreported as theorem dependencies.

References to earlier Problems or qualitative discussions are reported
separately from the 60-pair exact-label graph: 8->13 (Problem 8.7(a)), 3->18
(Problem 3.7), 6->18 (Problem 6.7), 12->23 (Problems 12.4), 23->26
(Problem 23.8), 6->27 (Problem 6.16), 24->27 (Problem 24.1), and 6->28
(qualitative magic-square discussion of Problem 6.4). The apparent 13->26
reference occurs only inside optional current-chapter Problem 26.2 and is
excluded from the core graph. The two apparent 8->20 and 8->21 matches are
citations to KieÅ‚basiÅ„ski and Schwetlick's external *Numerische Lineare
Algebra*, Lemma 8.2.11, not references to Higham Chapter 8. A code literal
`4.0*atan(1.0)` in Chapter 27 was also rejected as the false label `(1.0)`.

## Honest limitations and terminal classifications

- Unparameterized higher-order terms, visual tables, empirical performance
  reports, and unspecified algorithms are recorded, not converted to arbitrary
  predicates.
- Chapter 11's stronger corrected `n >= 2` Aasen theorem is useful follow-up,
  but it is not needed to terminally refute and correct the unrestricted row
  the PDF actually prints.
- Chapter 16 does not claim that supplied Schur factors were computed by a
  rounded QR iteration.
- Chapter 19 exposes the hidden inverse domain of (19.14).  Its actual RHS
  coefficient has a proved quadratic gamma index, but it does not claim that
  the source's unspecified `tilde-gamma` notation fixes that exact constant.
- Chapter 22's qualitative asymptotic/general-complex refinement sentence has
  no constant, threshold, or stability predicate.  Its exact finite Horner to
  Theorem 12.3 content is proved; the remaining prose is deferred.
- Existing terminal source discrepancies remain visible in their chapter
  ledgers, including Chapter 7's row-scaling wording, Chapter 8's reversed
  Lemma 8.8 inequality and Algorithm 8.13 initialization, Chapter 10's omitted
  domain, Chapter 14's signed-determinant/LINPACK wording, Chapter 15's
  normalized-dual convention, Chapters 20--21's rank/minimum statements,
  Chapter 26's zero Cardano branch, Chapter 27's universal Smith wording, and
  Chapter 28's false or underspecified normality/asymptotic claims.

## Verification record

- The frozen baseline passed a clean full build of 4,405 jobs before any repair
  was admitted as evidence.
- Every repaired module passed a focused build.  The broad repaired import cone
  passed 3,525 jobs; the strict Chapter 11 source route passed 3,063 jobs; and
  the Chapter 12 solver bridge passed 3,366 jobs.
- A clean production-root build of `LeanFpAnalysis.FP.Algorithms` passed all
  4,380 jobs.  The final repository-wide `lake build` then passed all 4,429
  jobs.  An earlier high-parallelism pass encountered Windows process exits in
  unchanged legacy modules; each affected module compiled successfully alone,
  and the warmed complete rerun passed with no Lean error.
- A dedicated `#print axioms` harness checked twenty headline closure
  endpoints spanning Chapters 3, 9, 11, 12, 14, 15, 19, and 22.  Every endpoint
  reported exactly `[propext, Classical.choice, Quot.sound]`.
- All 22 new production modules are reachable from
  `LeanFpAnalysis.FP.Algorithms` (twenty directly and two transitively).
- The 29 changed production Lean files contain no `sorry`, `admit`, axiom
  declarations, `unsafe`, `opaque`, or `native_decide`; the complete production
  declaration scan likewise reports zero `sorry`, `admit`, or `axiom`
  declarations.
- `git diff --check` passed apart from Git's platform line-ending notices.
- Immediately before the commit was prepared, `origin/main`, local `HEAD`, and
  a direct remote-ref query all still resolved to the frozen baseline
  `78cda8ba9debad7af00d2dd6a1b01f096551a488`; therefore no upstream changes
  required integration.  Verification of the pushed ref is recorded in the
  task handoff because a commit cannot truthfully contain its own final hash.

Untracked scratch files present before the audit were not used as evidence and
are not staged.
