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
- `NumStability.Algorithms.LinearSystems.Triangular` is a reviewed reusable
  algorithm-family entry point.
- `NumStability.Algorithms.Summation` is the complete published summation
  surface. Its `Recursive` and `Pairwise` family umbrellas preserve source
  reachability, while reusable consumers import their `.Core` leaves.
- `NumStability.Source` is the canonical source-correspondence entry point.
- `NumStability.Analysis.Summation` is an import-only family aggregate split
  into reusable `Signs` and `ErrorBounds` leaves.
- `NumStability.Analysis.Probability` is the reusable probability-analysis
  entry point. Its declaration-free `Probability.Gaussian` aggregate exposes
  the source-neutral `Probability.Gaussian.AbsoluteMoment` leaf.
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
  leaf. Chapter 14 owns `Problem13` and the declaration-free `Section05`
  aggregate for its Schulz-iteration leaves. The currently canonicalized
  Chapter 21 subset is the declaration-free `Chapter21` aggregate over
  `RowScalingInvariance`; the comprehensive historical Chapter 21 discovery
  surface remains `Algorithms.Underdetermined.Higham21` during migration.
  Chapter 12 uses the declaration-free
  `NumStability.Source.Higham.Chapter12` aggregate over the source leaves
  `IterativeRefinement`, `OmegaDiscontinuity`, and `Problem02`. Chapter 13's
  `DemmelSharpMultiplier` is a source leaf beside `Equation25` and `Table01`
  under the existing declaration-free `Chapter13` aggregate. Chapter 22 uses
  a declaration-free `Chapter22` aggregate over `VandermondeSystems`,
  `MonomialResidual`, `Problem07`, and the declaration-free `Section03`
  aggregate; that section owns the `RealRefinement` and
  `ComplexConfluentRefinement` source leaves. Chapter 27 uses a declaration-
  free `Chapter27` aggregate over `SoftwareEnvironment` and `Problem06`.
  Corresponding historical paths are compatibility wrappers listed in the
  executable compatibility map.
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
  point.
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
  executable, deliberately partial tier inventory and forbidden-edge gate.
- [`docs/architecture/reviews/`](docs/architecture/reviews/) contains the
  endpoint, performance, family, outlier, and physical-target decisions.
- [`docs/architecture/baselines/`](docs/architecture/baselines/) contains the
  generated machine-readable and human-readable graph snapshots.
- [`tools/architecture/`](tools/architecture/) and
  [`tools/benchmark/`](tools/benchmark/) reproduce the structural and build
  measurements.
