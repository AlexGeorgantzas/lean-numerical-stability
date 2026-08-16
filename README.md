# NumStability

A Lean 4 library for formally verified floating-point error analysis, following
Nicholas J. Higham's *Accuracy and Stability of Numerical Algorithms*
(2nd ed., SIAM, 2002), together with a randomized numerical linear algebra
(RandNLA) case study.

The library contains machine-checked material from **all 28 chapters** of
Higham. The tree contains **no `sorry` or `admit`, and no source-level `axiom`
or `constant` commands**. Sampled headline theorems depend only on the standard
`[propext, Classical.choice, Quot.sound]` axioms. The fresh audit makes every
selected core row terminal: precise claims are proved at source strength,
false claims have theorem-level counterexamples and faithful corrections, and
source text that does not determine a proposition is explicitly deferred.

## Floating-point model

The library uses an **abstract** floating-point model
([`FloatingPoint/Model.lean`](NumStability/FloatingPoint/Model.lean)), not a concrete IEEE-754
representation. An `FPModel` carries a unit roundoff `u` and rounding operations
`fl_add / fl_sub / fl_mul / fl_div / fl_sqrt`, each satisfying the standard model

```
fl(x ∘ y) = (x ∘ y)(1 + δ),   |δ| ≤ u
```

Because everything is parametric over `u` and the rounding operations, results
hold for **any** arithmetic satisfying the standard model. A concrete instance
`FPModel.exactWithUnitRoundoff` (operations exact, `δ = 0`, formal `u ≥ 0`) is
used to *prove obstructions* — for example, to refute overly strong norm or
factor-identification claims before replacing them with faithful statements.

## What's covered

Higham chapters 1–28, plus the RandNLA case study. Per-chapter status is tracked
in the ledgers under [`docs/source_coverage/`](docs/source_coverage/). The
authoritative from-scratch audit is the fresh PDF-first source-strength audit
[`docs/source_coverage/AUDIT_ch01-28_PDF_FIRST_2026-07-21.md`](docs/source_coverage/AUDIT_ch01-28_PDF_FIRST_2026-07-21.md).
It froze remote `main` at
`2bb76d004b7dddd0e6dfb61f84c0be8e6816fa19`, re-read all 28 chapter PDFs
(513 pages; corpus fingerprint recorded in the report), inventoried 165 named
body results and 585 numbered body equations, and then checked declaration
types and 60 exact-label producer-to-consumer chapter pairs independently of the
ledger conclusions. It distinguishes source-strength proofs, compiled source
counterexamples, undefined source statements, and external-citation deferrals.
Older reports are retained as historical records but are superseded by this
rerun, which found additional source-strength and traceability gaps.

| Ch | Topic | Strict gate |
|----|-------|-------------|
| 1  | Principles of finite precision | PASS |
| 2  | Floating point arithmetic | PASS |
| 3  | Basics (dot products, `γ(n)`) | PASS |
| 4  | Summation | PASS |
| 5  | Polynomials (Horner) | PASS |
| 6  | Norms | PASS / SOURCE-DISCREPANCY |
| 7  | Perturbation theory for linear systems | PASS / SOURCE-DISCREPANCY |
| 8  | Triangular systems | PASS / SOURCE-DISCREPANCY / DEFER |
| 9  | LU factorization and linear equations | PASS |
| 10 | Cholesky factorization | PASS / SOURCE-DISCREPANCY |
| 11 | Symmetric indefinite / skew-symmetric systems | PASS / SOURCE-DISCREPANCY |
| 12 | Iterative refinement | PASS / DEFER |
| 13 | Block LU factorization | PASS |
| 14 | Matrix inversion | PASS / SOURCE-DISCREPANCY / DEFER |
| 15 | Condition number estimation | PASS / SOURCE-DISCREPANCY / DEFER |
| 16 | The Sylvester equation | PASS / DEFER |
| 17 | Stationary iterative methods | PASS |
| 18 | Matrix powers | PASS / DEFER |
| 19 | QR factorization | PASS / SOURCE-DISCREPANCY / DEFER (explicit domain) |
| 20 | The least squares problem | PASS / SOURCE-DISCREPANCY / DEFER (explicit domain) |
| 21 | Underdetermined systems | PASS / SOURCE-DISCREPANCY |
| 22 | Vandermonde systems | PASS / SOURCE-DISCREPANCY |
| 23 | Fast matrix multiplication | PASS / DEFER |
| 24 | The FFT and applications | PASS |
| 25 | Nonlinear systems and Newton's method | PASS / SOURCE-DISCREPANCY / DEFER |
| 26 | Automatic error analysis | PASS / SOURCE-DISCREPANCY / DEFER |
| 27 | Software issues in floating point | PASS / SOURCE-DISCREPANCY / DEFER |
| 28 | A gallery of test matrices | PASS / SOURCE-DISCREPANCY / DEFER |

Fresh result: **28 chapters terminal, 0 unresolved precise core rows**.
The explicit `DEFER` entries are source-level indeterminacy or external-citation
boundaries, not hidden proof holes.

`PASS` means every precise selected theorem, lemma, equation, and
implementation-facing claim is terminal under the audit rules. A
`SOURCE-DISCREPANCY` qualification means the printed statement is false and the
library contains both a theorem-level counterexample and a faithful correction;
it does not mean that the source formula was made provable by adding a hidden
hypothesis. Unparameterized higher-order notation, qualitative observations,
visual tables, and unspecified algorithms are explicitly inventoried and
deferred rather than converted into arbitrary propositions.

- **Chapter 11:** A bounded-search exact rook trace now constructs its schedule,
  permutations, `L`, and block-diagonal `D`, and proves the printed multiplier,
  pivot-block, growth, and Theorem 11.4 product bounds without caller-supplied
  rook certificates. Two compiled examples show why that exact growth statement
  cannot be attached unchanged to the present rounded mixed-pivot executor: its
  terminal `2 x 2` predicate is too weak, and even an aligned legal division
  rounding can exceed the exact bound. Theorem 11.8 is separately false as
  printed at `n=1`; the actual scalar Aasen execution and sharp corrected bound
  close that discrepancy. For Algorithm 11.1 complete pivoting, the new
  block-atomic sharp analysis proves Bunch's printed
  `3.07 (n-1)^0.446` comparison with the Chapter 9 (9.14) bound, exposes its
  separate order-one defect, and now closes the strict source-to-result route.
  Every symmetric nonsingular source matrix constructs an exact complete-
  search/symmetric-permutation/Schur trace; selected principal-minor
  determinant recurrences identify every whole-block pivot product, and
  Hadamard's inequality is derived for every contiguous whole-block segment.
  Thus
  `higham11_1_exists_exactBunchTrace_all_stageRatio_le_maxEntryNorm` returns
  the all-stage sharp ratio bound without caller-supplied trace, determinant,
  Hadamard, growth, or target certificates. Displayed equation (11.7) is also
  composed from the actual mixed block-LDLT/triangular-solve executor into the
  Chapter 9 (9.23) forward-error route.
- **Chapter 9:** the corrected 15-item PDF inventory includes the previously
  omitted Theorem 9.7. Its exact real extremal classification now starts from
  a constructed leading-row-on-ties GEPP trace and uses the full reduced-matrix
  growth history. Equation (9.14) likewise now bounds the supremum over the
  original matrix and every actual recursively generated GECP reduced stage,
  rather than only the exposed final upper factor. Theorems 9.8--9.11 now also have their printed complex-domain
  endpoints, including genuine complex GEPP traces and a full no-pivot
  diagonal-dominance history for Theorem 9.9.
- **Chapters 19 and 20:** literal rounded MGS and pivoted stored-QR / least-
  squares executors close their source-rate endpoints. Theorem 19.10 now starts
  from the canonical Givens matrix stage-fold and constructs orthogonal `Q`,
  `Rhat`, and `DeltaA` with the PDF's `m+n-2` columnwise coefficient. Computed
  nonbreakdown is stated only where it is the natural domain implicit in the
  source's “computed matrices” and “computed solution” language, not assumed as
  an error budget. Theorem 19.5 is now genuinely columnwise for the actual QR
  solve, (19.14) exposes its hidden inverse domain, and the Section 19.7
  componentwise residual is obtained by a direct Chapter 6 Lemma 6.6 bridge.
- **Chapters 10, 25, 26, and 28:** false printed formulas remain visible as checked
  source discrepancies with corrected theorems. Chapter 10 now includes the
  literal pivoted-Cholesky success/error chain, the premise-free Mathias
  completion theorem for (10.29), and an internally constructed complex
  no-pivot LU trace with exact growth `< 3`. The following unquantified
  qualitative backward-stability sentence is deferred, and a compiled complex
  `γ_n` counterexample prevents substituting a stronger real-field claim.
  Chapter 25's multiplicity-one bordered eigenproblem is closed. Chapter 26
  constructs the complex cube roots in Cardano's formula and proves the
  nonzero-branch handoff to the original cubic; a zero-branch counterexample
  records the missing qualification in the sentence after (26.5). Chapter 28's
  exact Hilbert rate and Gaussian-QR Haar law are otherwise closed.
- **Chapters 4, 8, 14, 15, 20, and 22:** the fresh repairs add the missing
  literal finite-format/executor, fan-in, finalized Gauss-Jordan, concrete
  rectangular general-`p` calculus, pivoted least-squares, and monomial-stage
  bridges instead of relying on target-bearing readiness or residual premises.
  The Chapter 14 result now includes Algorithm 14.4's literal rounded
  Doolittle phase, final divisions, derived uniform-inverse regularity, and
  source-domain constructor. The Chapter 12-to-22 refinement bridge now starts
  from the actual rounded real/complex differentiated-Horner residual instead
  of assuming a contraction conclusion; a compiled counterexample terminates
  the false literal (12.9) coefficient and the corrected route proves finite
  (12.8)--(12.10).
- **Cross-chapter bridges:** a second, exact-label projection corrected the
  initial mixed bridge count and exposed five additional composition gaps.
  The tree now gives the literal boundary-inclusive no-guard model (2.6) an
  actual dot-product path to (3.3)--(3.5), composes the concrete (7.31) safety
  vector with (15.1), connects
  the Chapter 9 complete-pivoting and forward-error producers to the precise
  Chapter 11 claims, gives the actual Chapter 9 LU solve a finite Chapter 12
  forward-error handoff, and supplies the Chapter 13 matrix-product handoff used by
  the block-WY analysis (19.17)--(19.22). Earlier-Problem and qualitative
  references are listed separately in the audit instead of inflating the
  exact-label graph.

The **RandNLA case study** is split into 19 reusable modules under
[`NumStability/Algorithms/RandomizedLinearAlgebra/`](NumStability/Algorithms/RandomizedLinearAlgebra)
and 18 exact source-correspondence modules under
[`NumStability/Source/DrineasMahoney/RandNLA2016/`](NumStability/Source/DrineasMahoney/RandNLA2016).
The historical 17-module
[`NumStability/Algorithms/RandNLA/`](NumStability/Algorithms/RandNLA) surface
remains available as a compatibility facade. Together they formalize the
meta-algorithms of Drineas and Mahoney's CACM survey
["RandNLA: Randomized Numerical Linear Algebra"](https://dl.acm.org/doi/10.1145/2842602)
— row/elementwise/leverage-score sampling, matrix concentration, low-rank
approximation, and least-squares preconditioning.

## Project statistics

Current accepted production-tree snapshot at successor checkpoint
[`C0003`](docs/architecture/phases/2026-08-repository-reorganization-completion/checkpoints/C0003-gates.md),
after the R03 floating-point-foundations/Higham Chapters 1--12 integration
(accepted code commit
`e20de2f931caa12221e708c341e9cb4f64d29b25`):

| Formalization size | Count |
|---|---:|
| Production Lean modules | **2,690** |
| Physical Lean source lines (including comments, blanks, and relocation padding) | **3,985,082** |
| Nonblank Lean source lines | **1,454,099** |
| Lean source bytes | **74,663,808** |
| Elaborated declarations | **56,903** |
| Theorem declarations (including source `theorem` and `lemma` commands) | **43,173** |
| Definition declarations | **11,978** |
| Inductive / constructor / recursor declarations | **509 / 734 / 509** |
| Public / private / internal declarations | **55,219 / 1,680 / 4** |
| Direct imports (internal / external) | **28,305 (17,193 / 11,112)** |
| Signature / body-or-proof / union declaration edges | **266,387 / 382,872 / 424,082** |
| Proof placeholders / top-level axiom or constant commands | **0** |

| Organization state | Count |
|---|---:|
| Import cycles | **0** |
| Classified modules | **2,436 (90.558%)** |
| Unclassified modules | **254** |
| Source / aggregate / compatibility modules | **1,088 / 377 / 420** |
| Reusable / internal / upstream / mixed modules | **544 / 2 / 5 / 0** |
| Compatibility wrappers / direct targets / import exceptions | **420 / 1,171 / 2** |
| Modules with documentation / missing module docs | **2,690 / 0** |
| Noncanonical names under review | **217** |
| Declaration-bearing umbrellas | **15** |
| Unsorted aggregate imports | **0** |
| Inventory rows complete / in scope / with debt | **2,356 / 334 / 310** |
| Reusable-to-Source reachability | **0** |

The source, import, tier, and declaration figures come from the hash-pinned
[`C0003 combined baseline`](docs/architecture/phases/2026-08-repository-reorganization-completion/baselines/C0003-combined.json),
generated by
[`tools/architecture/generate_baseline.py`](tools/architecture/generate_baseline.py).
Declaration counts are taken from Lean's elaborated format-2 graph, so theorem
declarations include both source `theorem` and `lemma` commands. Physical lines
include blank padding retained by byte-identical declaration relocation; the
nonblank count is the more useful source-volume comparison. The placeholder
result and live migration-debt values are enforced by
[`tools/architecture/check_layout.py`](tools/architecture/check_layout.py),
with compatibility and provenance checked separately.

The repository-reorganization successor remains in progress. C0003 accepts
R03, so M03 is accepted in addition to M01, M02, M11, and M12; bounded-phase
and repository-wide completion both remain incomplete. B0001/B0002 are
retired, their remote delivery refs are deleted, and their named worker worktrees were
removed after evidence archival. P0001/P0002 remain retired immutable
evidence, and R0001/R0002/R0002T are applied. B0003/R11 (QR and Chapter 19)
and B0004/R12 (Chapter 13 equations and Table 01) were delivered from exact
C0001 at immutable tips
`444a03259af510bdfe0921d1847b6add1b26ed73` and
`0726678a0f2db56e533f3b956a2f7f1531059d7d`, respectively. Separate true merge
commits `10169717ce4966e9963885b04e7b7733a3bc7730` and
`1495047a1befb1431f0501cf7a423c8e77f8661a` preserve both deliveries. The
reviewed same-C0001 R0003/R0004 union was applied exactly once after both merges,
together with its bounded Chapter 19 integration follow-ups. At C0002,
B0003/B0004 are retired, P0003/P0004 are retired immutable evidence, and
R0003/R0004 are applied. Acceptance-control commit
`c92c48a348a0e09e7d6ac9d4ff1db7673a027648` passed exact Lean CI run
31678412178 before the two remote delivery refs were deleted with exact-tip
leases and both clean named worker worktrees were removed without force after
evidence archival. Local delivery refs remain at their immutable tips. The
temporary `codex-local` authorization on `claude-lane` expired at C0002 and the
lane's single-operator boundary is restored. A fresh C0002 review selected
M03/R03 as a singleton: B0005 was planned at control commit
`fb5a021b4640dd595a99f7560ce252ad9836a5b6`, activated at
`1166874cb986d09f357d092f1171a31d7f8b2332`, expanded to a reviewed temporary
second operator (`claude-local`) at `c4f66cbdfdce6cf64d484be13290e7d2e60547f5`,
and route-amended for the fanIn7 private-closure repair at
`09b3962dc6ed18b6de6eea5dc4a0e0e7c8ba4bb7` — each with its own green Lean CI.
The R03 delivery (47 owners; 2,389 declarations, 2,132 relocated into 47
canonical destinations plus one documented bridge; 398 private
normalizations; 2,150 isolated tests) landed at immutable tip
`1f8ff4ca5b0b136901a2f47d43e1064dc09aa556` with parent exact C0002 and is
preserved by a true merge. The reviewed same-C0002 R0005 request (121 paths)
was applied exactly once after the merge. Against its expected postimage, 115
request paths are byte-exact and exactly six carry only their reviewed bounded
deviations: two aggregate-sort reconciliations, the two source
reclassifications, compatibility-row reconciliation, the layout ratchet, and
one consumer import-superset repair restoring a non-owner transitive supply
invisible to the typed declaration graph. The full merge-to-integration audit
separately accounts for exactly 21 additional paths: 11 aggregate follow-ups,
3 R03 test paths, 4 narrative documents, and 3 milestone-DAG/evidence paths.
At C0003, P0005 is retired immutable evidence and R0005 is applied. After exact
green control-chain head `a61438448beb02773ef6b0f4f50cbedf8d675d29`
passed Lean CI run 31833811860 (job 94875463331), `primary-human` retired B0005
at `2026-08-14T19:44:43Z`. Its exact remote delivery ref
`refs/heads/codex/reorg-completion-2026-08-r03-floating-point-foundations-ch01-ch12`
was deleted under an expected-tip lease and verified absent; seven ignored material artifacts
totaling 117,422,618 bytes were archived and verified under
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0003-R03-20260814`.
The named worktree
`C:\Users\qed_s\higham-worktrees\completion-r03-codex` was removed without
force after its `.lake`-only residue was moved recoverably under
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0003-R03-20260814\disposable-worktree-residue\completion-r03-codex`.
The local
delivery branch remains preserved at
`1f8ff4ca5b0b136901a2f47d43e1064dc09aa556`; the
[`R03 retirement review`](docs/architecture/phases/2026-08-repository-reorganization-completion/reviews/R03-retirement.md)
records the exact cleanup evidence. The temporary `claude-local`
second-operator authority on `codex-lane` expired at C0003. A fresh
exact-C0003 review then selected the R05+R06 pair — the only candidate pair
zero on all seven overlap dimensions — and planned B0006/R05 and B0007/R06
from exact C0003 code with whole-owner routes only, frozen shared requests
under a reviewed five-path union, identity projection replays, and a
reviewed temporary `claude-local` second-operator re-expansion scoped to
B0006 expiring at C0004. M07/R07 and every other unaccepted milestone remain
planned. The immutable R05 tip
`26e89100b3c7c8a64a41426d517cbd563a40db72` and R06 tip
`bfaf2ae917ed79165caa6cc58b3782984aa8d3d9`, each a direct child of the
accepted C0003 code, are now preserved by separate true merge commits
`538c7d248a0ccaec407a082ecb73b92d7c3faec2` and
`deee8e7ea0aeac7cfbd9fc2582eaf1f5b841fd0c`. After both merges, the reviewed
67-path R0006/R0007 union patch (SHA-256
`639DA03437C3FBAA6934E71B55EFE7D85DF51835D94978790C59162585690D4E`)
was applied exactly once from the common C0003 preimages; sequential request
replacement was not used. The original bounded follow-up ledger remains exactly
13 unique paths: 6 aggregate paths adding 31 direct-import edges over 29 unique
destinations, 3 milestone-DAG/evidence paths, and these 4 narrative paths. It
is disjoint from the later approved R0008 compatibility repair and remains the
immutable account of that earlier follow-up. R0008 repairs exactly 27 paths
(26 production importers plus `docs/architecture/COMPATIBILITY.md`): 4 replace
union postimages through an exact SHA-256 chain and 23 add new staged paths,
while `R0006-R0007-union-postimages.tsv` remains untouched. Variant A trims
only the `NumStability.Algorithms` umbrella's newly expanded Source imports,
preserving its `NumStability.Source.` direct-import ceiling at 49 without a
layout-baseline change. Registration covers 16 logical governance paths: 5
request artifacts, including the immutable `R0008-approval.md` addendum, 2
delivered branch records, the existing 3 milestone-DAG/evidence paths, these 4
narratives, and 2 validators. Seven were already staged in the 13-path ledger,
so registration adds 9 new paths. One newly staged stale Algorithms smoke-test
correction brings the candidate to 111 staged paths in all (78 before R0008 +
23 repair-only + 9 registration-only + 1 smoke correction). B0006 and B0007
are recorded delivered at their exact tips but remain unaccepted and unretired;
both worker refs and worktrees remain intact. The earlier battery exposed one
stale Source-only Algorithms `#check`; it was removed under D1 and the targeted
smoke file passes. The final exact-candidate evidence run
`.lake/integration-r05-r06-20260816T172806Z` passed all 11 gates with a stable
tree, including the full `NumStability`/`NumStabilityTest` build and `lake test`
(`DONE.json` SHA-256
`A5DA29ED1EE40AF2A4B3967EDB1981ECB041A5821D61EDD117F3F8A55735C166`).
Independent package and staged-diff audits are green. Exact-code Lean CI remains
the final C0004 proof obligation; the statistics above remain C0003-pinned until
C0004. The
[`active phase registry`](docs/architecture/phases/2026-08-repository-reorganization-completion/README.md)
is the authoritative status record; the predecessor C0008 phase remains
immutable historical evidence.

Everything is proved against Mathlib; sampled headline theorems depend only on
the standard `[propext, Classical.choice, Quot.sound]` axioms. The retained
evidence includes the
[`Phase 12 BlockLU semantic migration`](docs/architecture/migrations/2026-07-27-blocklu-semantic-phase12.md),
the [`complete Chapter 9 reconciliation`](docs/architecture/migrations/worker-ch09-closure-tail-e-migration.md),
the [`LSQ/Chapter 20 delivery`](docs/architecture/migrations/worker-lsq-ch20-delivery.md),
the [`QR/Chapter 19 delivery`](docs/architecture/migrations/worker-qr-ch19-delivery.md),
and the [`four-lane final integration`](docs/architecture/migrations/2026-07-31-four-lane-final-integration.md).
Those historical records, together with the C0003, C0002, C0001, and predecessor C0008 gate evidence, preserve the
finer ownership, source-span, dependency, isolated import-test, and axiom-probe
evidence behind the summary above.

## Building

Requires [`elan`](https://github.com/leanprover/elan). The repository pins
Lean/Lake in `lean-toolchain` (`leanprover/lean4:v4.29.0-rc3`) and pins Mathlib
to the exact revision recorded in `lake-manifest.json`. From a clone:

```bash
lake exe cache get   # download prebuilt Mathlib oleans — skipping this makes the build very slow
lake build NumStability
lake test
```

Build a single module, e.g.:

```bash
lake build NumStability.Algorithms.GaussJordan
```

If a fresh build fails fetching ProofWidgets, drop its release build in place:

```bash
curl -L https://github.com/leanprover-community/ProofWidgets4/releases/download/v0.0.90/ProofWidgets4.tar.gz -o /tmp/pw.tar.gz
mkdir -p .lake/build/packages/proofwidgets && tar xzf /tmp/pw.tar.gz -C .lake/build/packages/proofwidgets
```

## Library organization

Choose the narrowest entry point that matches the material you need:

- `NumStability.Core` contains the foundational floating-point model and core
  analysis infrastructure.
- `NumStability.Algorithms.Arithmetic.DotProduct.NoGuard` is the reusable
  no-guard dot-product surface; its `Core` and `Tree` leaves avoid importing
  source-specific Higham correspondence.
- `NumStability.Algorithms.Summation` is the public umbrella for the summation
  algorithm family. Reusable recursive and pairwise consumers should choose
  `Summation.Recursive.Core` or `Summation.Pairwise.Core`. Reusable insertion
  consumers should choose `Insertion.ActiveList`, `Insertion.Executor`,
  `Insertion.Schedule`, `Insertion.RunningError`, or
  `Insertion.ScheduleExecution`; the broad family modules also preserve their
  supported Chapter 4 source declarations.
- `NumStability.Algorithms.LinearSystems.Triangular` is the reusable umbrella
  for forward/back substitution and triangular-system error bounds.
- `NumStability.Algorithms.LinearSystems.QR` is the reusable QR umbrella;
  numbered Chapter 19 correspondence is under
  `NumStability.Source.Higham.Chapter19`. The former `Algorithms.QR.*` paths
  remain import-only compatibility shims.
- Least-squares algorithms and perturbation analysis are organized under
  `NumStability.Algorithms.LinearSystems.LeastSquares` and
  `NumStability.Analysis.Perturbation.LeastSquares`, with numbered Chapter 20
  material under `NumStability.Source.Higham.Chapter20`. Eleven tightly
  source-coupled leaves are explicitly classified as source rather than being
  hidden behind a reusable-family exemption.
- Symmetric-indefinite reusable structure is exposed through
  `NumStability.Algorithms.LinearSystems.SymmetricIndefinite`; Chapter 11
  correspondence is split under `NumStability.Source.Higham.Chapter11`. The
  historical `Algorithms.HighamChapter11` owner is now an import-only facade.
- `NumStability.Analysis.Summation` is the complete summation-analysis umbrella;
  `NumStability.Analysis.Summation.Signs` is its reusable sign/absolute-value
  leaf, while `ErrorBounds` contains the reusable conditioning and rounded-fold
  error theory.
- `NumStability.Analysis.Equidistribution` is the reusable equidistribution
  umbrella. Its `AddCircle` leaf provides finite-orbit measures, Fourier/Haar
  convergence, and ball and half-open-arc frequency theorems.
- `NumStability.Analysis.LeadingDigits` is the reusable leading-digit umbrella
  over decimal predicates, decimal powers, empirical histograms, and the
  logarithmic distribution.
- The declaration-free reusable norm family entry points are
  `NumStability.Analysis.Asymptotics`, `LinearOperators`, `OperatorNorms`,
  `VectorNorms`, `MatrixNorms`, `SingularValues`, and `Conditioning`. Their
  semantic leaves separate foundational definitions, attainment, duality,
  interpolation, matrix comparisons and Lp norms, singular values,
  realification, spectral-radius bounds, and perturbation conditioning.
  `SingularValues.WeylMirsky` remains the independently extracted generic
  all-index perturbation API used by Higham Chapter 14 Problem 14.15 and by
  reusable least-squares analysis.
- `NumStability.Analysis.Norms.Core` is now a declaration-free reusable
  aggregate over the 20 Phase 11B1 reusable owners. The path remains importable
  for the former reusable subset, but numbered Chapter 6 results now live under
  `NumStability.Source.Higham.Chapter06`; the historical
  `NumStability.Analysis.Norms` path remains an import-only two-target facade
  over Core and `NumStability.Source.Higham.Chapter06.Norms`.
- `NumStability.Analysis.Probability` is the reusable probability-analysis
  umbrella. Its `Probability.Gaussian` aggregate exposes
  `Probability.Gaussian.AbsoluteMoment`, the source-neutral Gaussian first-
  absolute-moment API used by the Chapter 28 Ginibre development. Its
  `Probability.Haar` aggregate exposes
  `Probability.Haar.HomogeneousSpaceUniqueness`, the generic Haar-fiber and
  invariant-probability uniqueness API used by the Chapter 28 Stewart proof.
- `NumStability.Algorithms.MatrixEquations.Sylvester` is the reusable
  Sylvester/Lyapunov entry point, with narrow equation, backward-error,
  conditioning, perturbation, and generalized-equation families. Reusable
  Schur and inverse-operator results live under
  `NumStability.Analysis.LinearOperators.Schur` and
  `NumStability.Analysis.SingularValues.InverseBounds`; numbered source
  correspondence lives under `NumStability.Source.Higham.Chapter16` and
  `Chapter18`. `NumStability.Algorithms.Sylvester` remains the complete
  historical discovery surface during migration.
- `NumStability.Algorithms.FastMatMul.Recurrences` is the reusable Strassen and
  Winograd--Strassen recurrence API. `NumStability.Algorithms.FastMatMul` is the
  complete historical family aggregate; unsupported declarations inherited
  from that path live in `FastMatMul.Internal.LegacyBounds`.
- `NumStability.Source` is the canonical umbrella for source-faithful material.
- `NumStability.Source.Higham` collects Higham chapter results and explicit
  cross-chapter bridges. The complete nonrandom-rounding correspondence is
  `NumStability.Source.Higham.Chapter01.Section17`; its five semantic leaves
  separate Horner evaluation, interval propagation, grid variation, stored
  IEEE-double inputs, and the final error-spread result. The historical
  `Analysis.NonrandomRounding*` paths are import-only compatibility shims. For
  Chapter 2, Problem 2.2 is the canonical
  `NumStability.Source.Higham.Chapter02.Problem02` leaf. Problem 2.11's source
  samples are in `Chapter02.Problem11`, with reusable decimal and empirical
  support under `Analysis.LeadingDigits`. The Section 2.7 power-frequency
  conclusion is `Chapter02.Section07.PowerLeadingDigits`; its reusable
  AddCircle and decimal-power development lives under `Analysis`. The
  declaration-free `Chapter06.Norms` aggregate exposes Problems 6.1, 6.5,
  6.9, and 6.10 together with the literal ambient-radius form of Theorem 6.4.
  Phase 11B2 adds `Lemma06`, `Equation01`, and `Equation02`; four semantic
  leaves below `Chapter06.Asides`; and the `BlockAntidiagonalNorm.InducedLp`
  and `BlockAntidiagonalNorm.OperatorTwo` leaves. The declaration-free
  `Asides` aggregate preserves the six-topic historical asides surface, while
  `BlockAntidiagonalNorm` groups its two norm results. The declaration-free
  `Chapter06` aggregate imports `Norms`, `Asides`, `BlockAntidiagonalNorm`,
  `Equation02`, and `Lemma06`. The four former Algorithms/Analysis owners are
  exact compatibility wrappers, not preferred declaration homes.
  Chapter 14
  contains `Problem13`, the canonical `Problem14` owner for Problem 14.14's
  Hyman determinant result, `Problem15` for the source-specific determinant
  bound and counterexample, and the declaration-free `Section05` Schulz family
  aggregate. The generic singular-value perturbation support for Problem 14.15
  lives in reusable `Analysis.SingularValues.WeylMirsky`; the former
  `Algorithms.Chapter14Problem1415Weyl` path is an import-only wrapper. Chapter
  21 now contains `RowScalingInvariance`, the declaration-free `Theorem03`
  aggregate over `Theorem03.Attainment`, and the declaration-free `Theorem04`
  aggregate over `Theorem04.RowwiseBackwardError`. The former
  `Algorithms.Underdetermined.Higham21RowwiseMeasure` path is an import-only
  wrapper. The comprehensive historical Chapter 21 discovery surface remains
  `NumStability.Algorithms.Underdetermined.Higham21` during migration. Chapter
  28 now has a declaration-free canonical aggregate; its `Equation02`
  aggregate exposes the source-specific `RatioDiscrepancy` leaf, while the
  former `Algorithms.TestMatrices.Higham28HilbertRatioDiscrepancy` path is an
  import-only wrapper. That leaf deliberately still imports the historical
  `Higham28HilbertAsymptotic` dependency until the wider Hilbert family moves.
  The homogeneous-space uniqueness lemmas remain source-independent under
  `Analysis.Probability.Haar`. These are dependency-contained frontiers, not
  completed migrations of the broader chapter families. For
  fast matrix multiplication, import
  `NumStability.Source.Higham.Chapter23` or one of its semantic theorem,
  equation, algorithm, or problem leaves. Chapters 12, 22, and 27 now have
  complete declaration-free aggregates at
  `NumStability.Source.Higham.Chapter12`,
  `NumStability.Source.Higham.Chapter22`, and
  `NumStability.Source.Higham.Chapter27`;
  Chapter 22's real and complex refinement leaves are grouped by the
  declaration-free `NumStability.Source.Higham.Chapter22.Section03` aggregate.
  Reusable block-LU mathematics is published from
  `NumStability.Algorithms.LinearSystems.LU.BlockLU`. Higham Chapter 13's
  numbered block-LU correspondence is published from the declaration-free
  `NumStability.Source.Higham.Chapter13.BlockLU` aggregate, with narrower
  section, theorem, lemma, and Problem 13.4 family aggregates below it.
  `NumStability.Source.Higham.Chapter13` combines that source surface with the
  independent `DemmelSharpMultiplier` leaf. The historical
  `NumStability.Algorithms.LU.BlockLU` path remains importable as a two-target
  compatibility facade; new code should choose the reusable or source path
  explicitly. The follow-on sibling migration also reduces the ten former
  declaration-bearing `Algorithms.LU.BlockLU*` paths to tested compatibility
  wrappers over 22 reusable and Chapter 13 semantic destinations.
  Reusable Cholesky factorization, solve, perturbation, rounded-factorization,
  positive-semidefinite, and error-analysis APIs are collected by
  `NumStability.Algorithms.LinearSystems.Cholesky`; their numbered Chapter 10
  counterparts are collected by `NumStability.Source.Higham.Chapter10`.
- `NumStability.Higham` is the historical compatibility entry point; new code
  should import `NumStability.Source.Higham`.
- `NumStability.All` exposes the complete supported library surface.
- `NumStability` currently remains a compatibility entry point for
  `NumStability.All`.

New code should import canonical semantic paths. Historical paths listed in
the compatibility manifest are import-only shims, not preferred APIs; retained
aggregates continue to provide their documented broad surfaces. See
[`ARCHITECTURE.md`](ARCHITECTURE.md) for the layer contract,
[`docs/architecture/NAMING.md`](docs/architecture/NAMING.md) for naming and
module-placement rules, [`CONTRIBUTING.md`](CONTRIBUTING.md) for the required
checks,
[`docs/architecture/MIGRATION.md`](docs/architecture/MIGRATION.md) for the
evidence-gated migration sequence, and
[`docs/architecture/COMPATIBILITY.md`](docs/architecture/COMPATIBILITY.md) for
the old-to-new path map and removal policy. The
[`docs/README.md`](docs/README.md) index distinguishes current policy from
dated audit evidence.

This is an enforced migration state, not a claim that the whole historical
corpus is already Mathlib-style. The C0003 ratchet records 254 unclassified
modules, zero mixed modules, zero missing module docs, 217 noncanonical names,
and 15 reviewed declaration-bearing umbrellas across 310 distinct
residual-debt rows. CI enforces the per-prefix
direct-import ceilings recorded in `docs/architecture/layout-exceptions.json`
and prevents these queues from growing while each dependency-contained family
is migrated. In particular, the Chapter 14, Chapter 21, and Chapter 28 moves
above establish only their documented frontiers; their broader historical
families remain in the migration queue.

## Use as a dependency

Add to your `lakefile.toml`:

```toml
[[require]]
name = "numStability"
git = "https://github.com/AlexGeorgantzas/lean-numerical-stability"
rev = "main"
```

For a narrow dependency, import the canonical family or leaf named above. The
following deliberately uses `import NumStability`, the historical complete
compatibility surface, to make all supported declarations available:

```lean
import NumStability
open NumStability

variable (fp : FPModel) (n : ℕ)

#check gamma fp n                -- γ(n) = nu / (1 - nu)
#check dotProduct_error_bound    -- |fl(x·y) - x·y| ≤ γ(n)·Σ|xᵢ||yᵢ|
#check backSub_backward_error    -- (U + ΔU)x̂ = b, |ΔU| ≤ γ(n)|U|
#check lu_solve_backward_error   -- (A + ΔA)x̂ = b, |ΔA| ≤ (3γ(n)+γ(n)²)|L̂||Û|
```

## Project structure

```
NumStability.lean              -- historical complete compatibility entry point
NumStability/
  Core.lean                    -- foundational reusable entry point
  All.lean                     -- complete supported library surface
  FloatingPoint.lean           -- floating-point foundations umbrella
  FloatingPoint/
    IEEE.lean                  -- IEEE-facing operations umbrella
    IEEE/
      NaiveMaximum.lean        -- reusable maximum/NaN comparison API
    Model.lean                 -- the abstract floating-point model
  Analysis.lean                -- complete analysis aggregate, including legacy work
  Analysis/                    -- stability, perturbation theory, matrix algebra,
                               --   norms, concentration, and probability
    Asymptotics.lean           -- reusable asymptotic-bound umbrella
    Conditioning.lean          -- reusable conditioning umbrella
    Equidistribution.lean      -- reusable equidistribution umbrella
    Equidistribution/
      AddCircle.lean           -- Fourier/Haar orbit equidistribution API
    LeadingDigits.lean         -- reusable leading-digit umbrella
    LeadingDigits/
      Decimal.lean             -- decimal leading-digit predicate
      DecimalPowers.lean       -- powers, logarithms, and decimal arcs
      Empirical.lean           -- finite empirical digit histograms
      LogarithmicDistribution.lean -- logarithmic leading-digit law
    LinearOperators.lean       -- reusable linear-operator umbrella
    MatrixNorms.lean           -- reusable matrix-norm umbrella
    Norms.lean                 -- historical two-target compatibility facade
    Norms/
      Core.lean                -- declaration-free legacy Core surface
    OperatorNorms.lean         -- reusable operator-norm umbrella
    Probability.lean           -- reusable probability-analysis umbrella
    Probability/
      Gaussian.lean            -- Gaussian-analysis umbrella
      Gaussian/AbsoluteMoment.lean -- reusable Gaussian moment API
      Haar.lean                -- reusable Haar-analysis umbrella
      Haar/HomogeneousSpaceUniqueness.lean -- invariant-measure uniqueness
    SingularValues.lean        -- reusable singular-value umbrella
    Summation.lean             -- import-only summation-analysis umbrella
    Summation/
      Signs.lean               -- reusable sign and absolute-sum API
      ErrorBounds.lean         -- reusable conditioning and error-bound layer
    VectorNorms.lean           -- reusable vector-norm umbrella
  Algorithms.lean              -- numerical-algorithm umbrella
  Algorithms/                  -- algorithm formalizations, with clusters such as
                               --   LU, QR, Cholesky, RandNLA, and TestMatrices
    Arithmetic/DotProduct/
      NoGuard.lean             -- reusable no-guard dot-product umbrella
    Summation.lean             -- complete summation-family umbrella
    Summation/
      Insertion.lean           -- complete insertion-family umbrella
      Insertion/               -- active list, executor, schedule, and error layers
    FastMatMul.lean             -- complete historical fast-multiplication aggregate
    FastMatMul/
      Recurrences.lean         -- reusable recurrence API
      Internal/LegacyBounds.lean -- unsupported historical bounds
  Source.lean                  -- canonical source-faithful umbrella
  Source/
    Higham.lean                -- Higham source umbrella
    Higham/
      Chapter01/
      Chapter02/
        Problem11.lean         -- Problem 2.11 source samples and locator
        Section07.lean         -- declaration-free Section 2.7 aggregate
        Section07/PowerLeadingDigits.lean -- power-frequency source conclusion
      Chapter04/
      Chapter06.lean           -- complete current Chapter 6 aggregate
      Chapter06/
        Asides.lean            -- six-topic historical-asides aggregate
        Asides/
          ConditionNumberBounds.lean
          EuclideanNormDifferentiability.lean
          MaxNormInconsistency.lean
          UnitaryInvariance.lean
        BlockAntidiagonalNorm.lean -- induced-Lp/operator-2 family aggregate
        BlockAntidiagonalNorm/
          InducedLp.lean
          OperatorTwo.lean
        Equation01.lean        -- Hölder equality and endpoint witnesses
        Equation02.lean        -- dual-of-dual source correspondence
        Lemma06.lean           -- Lemma 6.6 parts (a), (c), and sharpness
        Norms.lean             -- numbered norm-result aggregate
        Problem01.lean         -- Problem 6.1 source closure
        Problem05.lean         -- Problem 6.5 source closure
        Problem09.lean         -- Problem 6.9 source closure
        Problem10.lean         -- Problem 6.10 source closure
        Theorem04.lean         -- literal ambient-radius Theorem 6.4
      Chapter08/, Chapter10/
      Chapter11.lean          -- declaration-free Chapter 11 aggregate
      Chapter11/              -- symmetric-indefinite/skew source owners
      Chapter12/, Chapter13/, Chapter17/
      Chapter19.lean          -- declaration-free Chapter 19 QR aggregate
      Chapter19/              -- numbered QR source owners
      Chapter20.lean          -- declaration-free Chapter 20 LSQ aggregate
      Chapter20/              -- numbered least-squares source owners
      Chapter14/
        Problem14.lean         -- Problem 14.14 Hyman determinant result
      Chapter21/
        Theorem03.lean         -- declaration-free Theorem 21.3 aggregate
        Theorem03/Attainment.lean -- attainment and nonattainment boundary
      Chapter22/, Chapter23/, Chapter24/, Chapter25/, Chapter26/, Chapter27/
                               -- canonical numbered source correspondence
      CrossChapter/            -- explicitly cross-chapter source bridges
  Higham.lean                  -- historical import-only compatibility entry point
docs/
  source_coverage/            -- per-chapter coverage ledgers + fresh ch01–28 audit
  chapterNN/                  -- detailed source inventories / proof ledgers
```

## Exact algebra and matrix norms

Mathlib is the source of truth for exact algebra and norms; new APIs use Mathlib
notation directly (e.g. `‖A‖` under the appropriate matrix-norm scope) and the
alias `RMat m n := Matrix (Fin m) (Fin n) ℝ`. The legacy algorithm layer uses
function-shaped matrices `RMatFn m n := Fin m → Fin n → ℝ` with documented
compatibility wrappers (`frobNorm`, `infNorm`) that coerce through `Matrix.of`
and reuse Mathlib's norms — they are not independent norm definitions.

## References

- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
  SIAM, 2002.
- P. Drineas and M. W. Mahoney,
  ["RandNLA: Randomized Numerical Linear Algebra"](https://dl.acm.org/doi/10.1145/2842602),
  *Communications of the ACM* 59(6), 80–90, 2016.

## Roadmap

The selected formalization core scope is closed; the repository-organization
migration is not. Phase 11B1 split the transitional `Analysis.Norms.Core`
owner, and Phase 11B2 moved the remaining audited Chapter 6 source owners.
Phase 12 has now split the historical 82k-line `Algorithms.LU.BlockLU`
declaration owner into reusable and 68-owner Chapter 13 source surfaces, then
migrated all ten declaration-bearing BlockLU siblings into 22 semantic owners
while preserving every old import as a compatibility facade. The completed
parallel checkpoint physically split all 4,420 Chapter 9 declarations into 20
canonical destinations, all 6,385 Chapter 11 declarations from 66 historical
owners into 73 destinations, all 3,991 QR declarations into 60 destinations,
and all 5,129 LSQ/Chapter 20 declarations into 73 destinations. The QR-to-LSQ
ownership handoff is resolved and the strict classified graph has no reusable-
to-source or reusable-to-mixed path. The first post-integration cleanup also
classified 42 declaration-free Chapter 19 facades and normalized all production
consumers to their canonical imports. C0005 subsequently accepted the W03 split
of 26 Cholesky/Chapter 10 owners into 61 canonical production modules and the
W05 split of 10 Sylvester/Schur owners into 79 canonical production modules,
while retaining every projection-required historical declaration and import.
C0006 then accepted the W06 split of 67 Chapter 16/18 owners into 176 canonical
production modules and the W08 split of 42 matrix-inversion/Chapter 14 owners
into 73 canonical production modules. C0007 then accepted the W04 split of 29
Chapter 21/underdetermined owners into 84 canonical production modules, the W09
split of 72 test-matrix/Chapter 28 owners into 93 canonical production modules,
and the W11 split of 18 RandNLA owners into 37 canonical production modules.
C0008 then accepted the W07 split of 5 Chapter 17/stationary-iteration owners
into 34 canonical production modules and the W10 split of 27 Chapter 15/
norm-estimation owners into 96 canonical production modules. M90 is ready but
remains unactivated. Successor C0001 then accepted R01/R02 cleanup of 44
residual owners into 38 new production modules. Those delivery branches are
retired. C0002 then accepted the exact-C0001 R11/R12 deliveries, reorganizing
68 residual owners and adding 11 canonical production modules. B0003/B0004 are
retired: their exact remote refs were deleted after acceptance-control CI went
green, their named worker worktrees were removed after evidence archival, and
their local delivery refs remain preserved. C0003 now accepts the exact-C0002
R03 delivery, reorganizing 47 residual owners into canonical floating-point
foundations and Higham Chapters 1--12 surfaces. B0005 is retired after exact
green control-chain CI, expected-tip remote-ref deletion, evidence archival,
and removal of its named worktree without force; its local delivery branch
remains preserved at `1f8ff4ca5b0b136901a2f47d43e1064dc09aa556`. P0005 is
retired and R0005 is applied. The current C0003 counts are authoritative.
Subsequent accepted batches must reduce the current 254
unclassified modules, 217 noncanonical names, 15 declaration-bearing
umbrellas, and the remaining reviewed giant-file outliers; mixed-tier and
missing-module-documentation debt are both zero.
The sequence and safety gates are tracked in
[`docs/architecture/MIGRATION.md`](docs/architecture/MIGRATION.md), with exact
ownership, checkpoints, and wave dependencies in the active
[`August 2026 successor phase contract`](docs/architecture/phases/2026-08-repository-reorganization-completion/README.md).

## License

Except where an individual file states otherwise, NumStability is licensed
under the [MIT License](LICENSE). Files carrying an Apache-2.0 notice are
licensed under the [Apache License, Version 2.0](LICENSES/Apache-2.0.txt).
Third-party attribution and upstream references are recorded in
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

Citation metadata is available in [`CITATION.cff`](CITATION.cff).
