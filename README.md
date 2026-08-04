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

The **RandNLA case study**
([`NumStability/Algorithms/RandNLA/`](NumStability/Algorithms/RandNLA), 17 modules)
formalizes the meta-algorithms of Drineas and Mahoney's CACM survey
["RandNLA: Randomized Numerical Linear Algebra"](https://dl.acm.org/doi/10.1145/2842602)
— row/elementwise/leverage-score sampling, matrix concentration, low-rank
approximation, and least-squares preconditioning.

## Project statistics

Current accepted production-tree snapshot at checkpoint
[`C0006`](docs/architecture/phases/2026-08-repository-reorganization/checkpoints/C0006-gates.md),
after the W06 Chapter 16/18 remainder and W08 matrix-inversion/Chapter 14
integration (accepted code commit `a32095e6e50189f7dcc39312bb4c6a36f421fab5`):

| Formalization size | Count |
|---|---:|
| Production Lean modules | **2,242** |
| Physical Lean source lines (including comments, blanks, and relocation padding) | **3,275,409** |
| Nonblank Lean source lines | **1,432,575** |
| Lean source bytes | **72,841,048** |
| Elaborated declarations | **56,903** |
| Theorem declarations (including source `theorem` and `lemma` commands) | **43,173** |
| Definition declarations | **11,978** |
| Inductive / constructor / recursor declarations | **509 / 734 / 509** |
| Public / private / internal declarations | **55,219 / 1,680 / 4** |
| Direct imports (internal / external) | **16,654 (11,206 / 5,448)** |
| Signature / body-or-proof / union declaration edges | **266,387 / 382,872 / 424,082** |
| Full library and smoke-test build graph | **7,820 jobs** |
| Proof placeholders / top-level axiom or constant commands | **0** |

| Organization state | Count |
|---|---:|
| Import cycles | **0** |
| Classified modules | **1,933 (86.218%)** |
| Unclassified modules | **309** |
| Source / aggregate / compatibility modules | **824 / 361 / 337** |
| Reusable / internal / upstream / mixed modules | **395 / 2 / 5 / 9** |
| Compatibility wrappers / direct targets | **337 / 685** |
| Modules with documentation / missing module docs | **2,125 / 117** |
| Noncanonical names under review | **261** |
| Declaration-bearing umbrellas | **21** |
| Reusable-to-Source reachability | **0** |
| Provenance contract | **197 Apache files / 5 upstream modules** |

The source, import, tier, and declaration figures come from the hash-pinned
[`C0006 combined baseline`](docs/architecture/phases/2026-08-repository-reorganization/baselines/C0006-combined.json),
generated by
[`tools/architecture/generate_baseline.py`](tools/architecture/generate_baseline.py).
Declaration counts are taken from Lean's elaborated format-2 graph, so theorem
declarations include both source `theorem` and `lemma` commands. Physical lines
include blank padding retained by byte-identical declaration relocation; the
nonblank count is the more useful source-volume comparison. The placeholder
result and live migration-debt values are enforced by
[`tools/architecture/check_layout.py`](tools/architecture/check_layout.py),
with compatibility and provenance checked separately.

The repository-reorganization phase remains in progress. C0006 accepts W06 and
W08, so M06 and M08 are accepted; M04, M07, M09, and M11 are ready but have not
been activated. After the C0006 acceptance-control commit passed Lean CI, the
two exact W06/W08 remote delivery refs were retired at
`2026-08-04T13:33:21Z`; local worker branches and worktrees remain preserved. The
[`active phase registry`](docs/architecture/phases/2026-08-repository-reorganization/README.md)
is the authoritative status record.

Everything is proved against Mathlib; sampled headline theorems depend only on
the standard `[propext, Classical.choice, Quot.sound]` axioms. The retained
evidence includes the
[`Phase 12 BlockLU semantic migration`](docs/architecture/migrations/2026-07-27-blocklu-semantic-phase12.md),
the [`complete Chapter 9 reconciliation`](docs/architecture/migrations/worker-ch09-closure-tail-e-migration.md),
the [`LSQ/Chapter 20 delivery`](docs/architecture/migrations/worker-lsq-ch20-delivery.md),
the [`QR/Chapter 19 delivery`](docs/architecture/migrations/worker-qr-ch19-delivery.md),
and the [`four-lane final integration`](docs/architecture/migrations/2026-07-31-four-lane-final-integration.md).
Those historical records, together with the C0006 gate evidence, preserve the
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
corpus is already Mathlib-style. The C0006 ratchet records 309 unclassified
modules, 9 mixed modules, 117 missing module docs, 261 noncanonical names, and
21 reviewed declaration-bearing umbrellas. CI enforces the per-prefix
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
into 73 canonical production modules. M04, M07, M09, and M11 are ready but
remain unactivated. Subsequent accepted batches must reduce the current 309
unclassified modules, 261 noncanonical names, 117 missing module docs, and the
remaining reviewed giant-file outliers. The
sequence and safety gates are tracked in
[`docs/architecture/MIGRATION.md`](docs/architecture/MIGRATION.md), with exact
ownership, checkpoints, and wave dependencies in the active
[`August 2026 phase contract`](docs/architecture/phases/2026-08-repository-reorganization/README.md).

## License

Except where an individual file states otherwise, NumStability is licensed
under the [MIT License](LICENSE). Files carrying an Apache-2.0 notice are
licensed under the [Apache License, Version 2.0](LICENSES/Apache-2.0.txt).
Third-party attribution and upstream references are recorded in
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

Citation metadata is available in [`CITATION.cff`](CITATION.cff).
