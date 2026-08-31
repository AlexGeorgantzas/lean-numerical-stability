# NumStability architecture

NumStability is both a reusable numerical-stability library and a machine-checked
correspondence with book sources.  Those roles share one repository, but they do
not share one public API tier.

## API tiers

Every declaration-bearing module belongs to exactly one primary tier.

1. **Reusable API** contains source-independent definitions, algorithms, and
   stability theorems intended for downstream use.
2. **Source correspondence** connects reusable declarations to numbered results,
   examples, discrepancies, and prose in a particular book or paper.
3. **Internal proof support** contains implementation lemmas and construction
   scaffolding that are not supported as downstream API.
4. **Tests and experiments** validate imports, declarations, examples, and
   performance without contributing library declarations.

Import-only forwarding modules and aggregate entry points have the structural
roles `compatibility` and `aggregate` in the executable tier inventory. They
are not destinations for new mathematical declarations.

Lean visibility is not an API promise.  A declaration is supported public API
only when its module and module documentation place it in tier 1 or tier 2.

## Dependency direction

The intended dependency graph is one-way:

```text
floating-point and exact mathematical foundations
                    |
                    v
generic error analysis and reusable algorithm specifications
                    |
                    v
rounded algorithms and their stability theorems
                    |
                    v
book/source correspondence, capstones, and discrepancies
                    |
                    v
tests, examples, audits, and benchmarks
```

A reusable module must not import a source-correspondence module.  Exact
algorithm specifications should not import their rounded-error proofs.  Tests
and audit tooling may import any public tier, but production modules must never
import tests or generated audit artifacts.

Temporary violations discovered during migration must be recorded in the
current architecture baseline and removed before a physical source library is
split from the reusable library.

## Entry points

- `NumStability.Core` is the deliberately small reusable foundation entry point.
- `NumStability.FloatingPoint` is the complete reusable floating-point entry
  point. Its declaration-free `FloatingPoint.IEEE` aggregate exposes reusable
  operations over the IEEE value-level model, beginning with
  `IEEE.NaiveMaximum`.
- `NumStability.Algorithms.LinearSystems` is the declaration-free reusable
  linear-systems entry point. It re-exports the canonical `Cholesky`,
  `CramersRule`, `GaussJordan`, `Iterative`, `IterativeRefinement`,
  `LeastSquares`, `LU`, `QR`, `SymmetricIndefinite`, `Triangular`, and
  `Underdetermined` families. As migration history, Phase 12 completed the
  reusable `LinearSystems.LU.BlockLU` umbrella over fifteen direct
  declaration-bearing leaves plus the `VaryingBlocks` subaggregate, whose five
  leaves support unequal block orders. The 1,695 source declarations cut over
  from the historical `Algorithms.LU.BlockLU` owner live below
  `Source.Higham.Chapter13.BlockLU`. Its follow-on moved 287 declarations from
  ten separately scoped siblings into 22 semantic destinations; all ten old
  sibling paths are now declaration-free compatibility wrappers.
- `NumStability.Algorithms.Summation` is the complete published summation
  surface. Its `Recursive` and `Pairwise` family umbrellas preserve source
  reachability, while reusable consumers import their `.Core` leaves.
- `NumStability.Source` is the canonical source-correspondence entry point.
- `NumStability.Analysis.Summation` is an import-only family aggregate split
  into reusable `Signs` and `ErrorBounds` leaves.
- `NumStability.Analysis.Equidistribution` is the reusable equidistribution
  entry point. Its `AddCircle` leaf contains the finite-orbit, Fourier, Haar,
  ball-frequency, and half-open-arc APIs.
- `NumStability.Analysis.LeadingDigits` is the reusable leading-digit entry
  point over `Decimal`, `DecimalPowers`, `Empirical`, and
  `LogarithmicDistribution`.
- `NumStability.Analysis.Asymptotics`, `LinearOperators`, `OperatorNorms`,
  `VectorNorms`, `MatrixNorms`, `SingularValues`, and `Conditioning` are the
  declaration-free reusable entry points produced or completed by the Phase
  11B1 norm split. Their 20 new reusable leaves own the generic asymptotic,
  operator, vector-norm, matrix-norm, singular-value, and conditioning APIs.
  Phase 12A adds `MatrixNorms.EntrywiseMaximum` as the owner of the reusable
  square and rectangular max-entry norm API.
  `SingularValues.WeylMirsky` remains the independently extracted
  source-neutral all-index perturbation API shared by Chapter 14 Problem 14.15
  and reusable least-squares analysis.
- `NumStability.Analysis.FirstOrder` is the declaration-free Phase 12A
  aggregate over reusable `AsymptoticFamilies` and `FixedPrecision` leaves.
- `NumStability.Analysis.Norms.Core` is now a declaration-free reusable
  aggregate over those 20 Phase 11B1 owners. The path remains importable for
  the former reusable subset; numbered Chapter 6 results are exposed by the
  dedicated `Source.Higham.Chapter06.Norms` source aggregate. The historical
  `NumStability.Analysis.Norms` path is an import-only facade over both.
- `NumStability.Analysis.Probability` is the reusable probability-analysis
  entry point. Its declaration-free `Probability.Gaussian` aggregate exposes
  the source-neutral `Probability.Gaussian.AbsoluteMoment` leaf. Its
  declaration-free `Probability.Haar` aggregate exposes
  `Probability.Haar.HomogeneousSpaceUniqueness`, whose generic Haar-fiber and
  invariant-probability uniqueness theorems support the Chapter 28 Stewart
  development without becoming source correspondence.
- `NumStability.Algorithms.Sylvester` is a complete family-discovery umbrella,
  not a claim that every Chapter 16 declaration is reusable mathematics.
- `NumStability.Algorithms.FastMatMul.Recurrences` is the reusable fast-
  multiplication recurrence leaf. `NumStability.Algorithms.FastMatMul` is the
  declaration-free complete-family aggregate retained for historical
  discovery; its internal legacy-bounds leaf is not supported downstream API.
- `NumStability.Source.Higham` is the canonical Higham correspondence entry
  point. Chapter 1 Section 1.17 is organized under
  `NumStability.Source.Higham.Chapter01.Section17`, with five semantic source
  leaves and declaration-free chapter and section aggregates. Historical
  `Analysis.NonrandomRounding*` paths are compatibility wrappers only.
  Chapter 2's Problem 2.2 surface lives in the canonical `Chapter02.Problem02`
  leaf. Printed Problem 2.22 is the `Chapter02.Problem22` source locator for
  reusable `FloatingPoint.IEEE.NaiveMaximum`; printed Problem 2.23 is the
  `Chapter02.Problem23` Heron leaf. The former Problem 22 canonical path
  temporarily re-exports Problem 23 to preserve its published import surface.
  Problem 2.11's source samples live in `Chapter02.Problem11`, while its
  reusable classifier and empirical-distribution support live below
  `Analysis.LeadingDigits`. The Section 2.7 power-frequency conclusion is the
  `Chapter02.Section07.PowerLeadingDigits` leaf beneath a declaration-free
  `Section07` aggregate; its AddCircle and decimal-power machinery remains in
  reusable analysis. The former flat leading-digit Analysis paths are
  compatibility wrappers only.
  Chapter 6 has a declaration-free `Chapter06.Norms` aggregate over
  `Problem01`, `Problem05`, `Problem09`, `Problem10`, and `Theorem04`. Phase
  11B2 completed the audited source tail as nine declaration-bearing leaves:
  `Lemma06`, `Equation01`, `Equation02`, four leaves below `Asides`, and
  `BlockAntidiagonalNorm.InducedLp` plus
  `BlockAntidiagonalNorm.OperatorTwo`. The declaration-free `Asides` aggregate
  preserves its historical six-topic surface by importing its four children,
  `Equation01`, and `BlockAntidiagonalNorm.OperatorTwo`; the declaration-free
  `BlockAntidiagonalNorm` aggregate imports both block-norm leaves. The chapter
  aggregate imports `Norms`, `Asides`, `BlockAntidiagonalNorm`, `Equation02`,
  and `Lemma06`. Historical `Algorithms.Chapter06Lemma66`,
  `Analysis.Higham6Asides`, `Analysis.Higham6BlockAntidiag`, and
  `Analysis.HighamChapter6Duality` are now exact one-target compatibility
  wrappers.
  Chapter 14's canonical source tree covers `Algorithm04`, `Corollary06`,
  `Corollary07`, `Discrepancies`, `Equation34`--`Equation36`,
  `Problem02`--`Problem05`, `Problem07`, `Problem08`, `Problem10`--`Problem15`
  (including Problem 14.14's Hyman determinant result and Problem 14.15's
  determinant bound and discrepancy witness), `Section01`--`Section03`,
  `Theorem05`, and the declaration-free `Section05` aggregate for its
  Schulz-iteration leaves. Generic Weyl--Mirsky support lives in reusable
  `Analysis.SingularValues.WeylMirsky`; the former combined Algorithms path is
  a compatibility wrapper. The canonical Chapter 21 source tree covers
  `Equation01`--`Equation11`, `Lemma02`, `Theorem01`, `Theorem03`,
  `Theorem04`, `RowScalingInvariance`, `Attainability`, `Corrections`, and
  `Section03`, exposed through the declaration-free 35-import `Chapter21`
  aggregate. `Theorem03.Attainment` owns the exact/closure attainment and
  scalar nonattainment refinements; `Theorem04.RowwiseBackwardError` owns the
  printed row-wise measure and quantitative gamma criterion. The canonical
  source tree is the comprehensive Chapter 21 surface; the historical
  `Algorithms.Underdetermined.Higham21` path is a declaration-free
  compatibility wrapper over it. Chapter 28 has a declaration-free canonical
  source aggregate over canonical `Equation01`--`Equation04` and
  `Section01`--`Section06` subtrees. Its declaration-free `Equation02`
  aggregate exposes the source-specific `RatioDiscrepancy` leaf, which imports
  reusable `Analysis.TestMatrices.Hilbert.HilbertAsymptotic` and
  `Chapter28.Equation02.DeterminantAsymptotics`. The homogeneous-space
  uniqueness support remains reusable `Analysis.Probability.Haar`, and the
  R09 wave relocated the remaining `Higham28*` Stewart and test-matrix owners,
  leaving the former `Algorithms.TestMatrices.Higham28HilbertAsymptotic` owner
  as an import-only compatibility wrapper. The Chapter 14, 21, and 28 families
  are migrated and classified: R09 canonicalized the TestMatrices surface, R10
  canonicalized the RandNLA surface, and the tier inventory records 0
  unclassified modules and 0 noncanonical names.
  Chapter 12 uses the declaration-free
  `NumStability.Source.Higham.Chapter12` aggregate over the source leaves
  `IterativeRefinement`, `OmegaDiscontinuity`, and `Problem02`. Chapter 13's
  declaration-free `BlockLU` aggregate has an exact 82-member direct-import
  surface: 81 declaration-bearing source owners and the declaration-free
  `Theorem02.VaryingBlocks` locator. Eleven declaration-free family umbrellas
  provide narrower discovery paths for
  Sections 13.1 and 13.3, Lemma 13.10, Theorems 13.2 and 13.6--13.8, and
  Problem 13.4. The chapter aggregate exposes `BlockLU` beside the independent
  `DemmelSharpMultiplier` leaf. The historical `Algorithms.LU.BlockLU` path is
  a declaration-free two-target compatibility facade over the reusable and
  source Block LU aggregates. Chapter 22 uses
  a declaration-free `Chapter22` aggregate over `VandermondeSystems`,
  `MonomialResidual`, `Problem07`, and the declaration-free `Section03`
  aggregate; that section owns the `RealRefinement` and
  `ComplexConfluentRefinement` source leaves. Chapter 27 uses a declaration-
  free `Chapter27` aggregate over `SoftwareEnvironment` and `Problem06`.
  Corresponding historical paths are compatibility wrappers listed in the
  executable compatibility map. The completed BlockLU migration preserves the
  former monolith and all ten sibling paths as declaration-free compatibility
  facades while production consumers use exact semantic owners.
  Chapter 23 is organized under
  `NumStability.Source.Higham.Chapter23`, with semantic base leaves and
  declaration-free Theorem 23.2, Theorem 23.3, Bini--Lotti, and combined
  3M--Strassen family aggregates. Historical `FastMatMul.Higham23*` paths are
  compatibility wrappers only.
- `NumStability.Higham` is a compatibility entry point forwarding to
  `NumStability.Source.Higham`.
- `NumStability.All` is the explicit complete-tree entry point.
- `NumStability.Algorithms` preserves its historical complete algorithm-layer
  surface, including source correspondence; it is not the pure reusable entry
  point. Its checked direct-import ceilings, recorded in
  [`docs/architecture/layout-exceptions.json`](docs/architecture/layout-exceptions.json),
  are 446 imports below `NumStability`, including 44 below
  `NumStability.Analysis` and 73 below `NumStability.Source`; these are
  enforced ceilings, not the live direct-import count.
- `NumStability` retains its historical complete-tree behavior through the
  compatibility window.

Changing the meaning of `import NumStability`, removing a forwarding module, or
renaming a supported declaration requires a planned breaking release.

## Placement rules

Choose a module path by mathematical role, not by the order in which the proof
was discovered.

- Put abstract rounding operations, formats, and unit-roundoff facts under
  `FloatingPoint/`.
- Put source-independent forward, backward, componentwise, perturbation, and
  conditioning theory under a reusable analysis area.
- Put exact matrix facts below algorithms that use them.
- Group algorithms first by mathematical family, then by semantic layer such as
  specification, exact execution, rounded execution, and stability.
- Put numbered chapter results, source aliases, source corrections,
  discrepancies, and cross-chapter traceability in the source-correspondence
  tier.  Cite the source in module and theorem docstrings.
- Keep proof-process labels such as `Closure`, `Bridge`, `Actual`, and `Source`
  out of the reusable API unless they name a genuine mathematical concept.

`Defs`, `Basic`, `Lemmas`, and `Internal` are not mandatory folder templates.
Use them only when they express a real dependency boundary.

Canonical path spelling and the target mathematical/source hierarchy are
defined in [`docs/architecture/NAMING.md`](docs/architecture/NAMING.md).
Historical spellings are permitted only for forwarding modules listed in the
compatibility manifest.

## Imports and module boundaries

- Production files import precise modules, never `NumStability` or
  `NumStability.All`.
- Umbrella files contain imports and documentation only.
- Keep imports alphabetized within public and private groups as files adopt the
  modern Lean module system.
- Prefer private declarations for proof support used only inside one module.
- Preserve old import paths with thin forwarding modules during migration.
- Split files at semantic and dependency boundaries, not arbitrary line counts.

File size is a review signal, not a success metric.  Compilation cost, edit
frequency, downstream rebuild fanout, conceptual cohesion, and graph cuts must
also support a split.

## Evidence and quality gates

Architecture changes are evaluated with:

- the module import graph and forbidden layer edges;
- declaration-signature dependencies, separate from proof-body dependencies;
- clean build time, peak memory, and repeated per-module timings;
- incremental rebuild time and downstream rebuild fanout;
- API/import smoke tests and compatibility-module tests;
- complete builds of every public entry point;
- lint, placeholder, and documentation checks.

CI enforces the source/import sanity scan plus entry-point and compatibility
builds. Full declaration baselines, controlled benchmarks, lint, placeholder,
and documentation audits are release gates run and recorded for architecture
migrations; they are not all repeated on every pull request.

Cross-module declaration utilization is diagnostic only.  Splitting a file can
increase it mechanically, so it must not be used as a reorganization target.
Apparent leaves and endpoint modules are review queues, not deletion evidence.

## Physical library split

The source-correspondence corpus remains in the same Lake library during the
first migration stages.  A separate physical library target is justified only
when all of the following hold:

1. the executable tier inventory has 100% coverage, no `mixed` modules, and no
   reusable module can reach a source module through the import graph;
2. the curated entry points and compatibility tests are stable;
3. clean and incremental measurements show a material benefit;
4. the additional package and release complexity is documented;
5. old import paths have an explicit compatibility and removal schedule.

## Migration evidence

- [`docs/architecture/MIGRATION.md`](docs/architecture/MIGRATION.md) defines
  the ordered evidence gates.
- [`docs/architecture/COMPATIBILITY.md`](docs/architecture/COMPATIBILITY.md)
  records forwarding paths and their removal policy.
- [`docs/architecture/TIERS.md`](docs/architecture/TIERS.md) explains the
  executable tier inventory, now complete over every production module, and
  the forbidden-edge gate.
- [`docs/architecture/reviews/`](docs/architecture/reviews/) contains the
  endpoint, performance, family, outlier, and physical-target decisions.
- [`docs/architecture/baselines/`](docs/architecture/baselines/) contains the
  generated machine-readable and human-readable graph snapshots.
- [`tools/architecture/`](tools/architecture/) and
  [`tools/benchmark/`](tools/benchmark/) reproduce the structural and build
  measurements.
