# Organization phase 10E build evidence (2026-07-26)

This record covers the semantic reorganization of three remaining Higham
frontiers: the Chapter 14 Hyman-determinant development, the Chapter 21
Theorem 21.3 attainment development, and the reusable Haar homogeneous-space
uniqueness API used by the Chapter 28 test-matrix work.

Development started from the Phase 10D checkpoint
`eabb6bdffaee9a42f96bdb9a37aa194d5421755d` on
`codex/organization-phase-10e-higham-frontiers`. The immutable ownership map
was committed before implementation as
`db7215bc20b3d0daf25de1e2c8ebefa47a215f35`.

Candidate-worktree and clean-commit validation are recorded separately. The
implementation revision is
`eead3f9a3880055435b39ba7dbee95ec5225cba7`. The architecture pair was then
captured from that clean revision and committed as
`b9d467c016c4f5cce29c375cb10cfa207c0dc217`. This evidence update changes no
Lean declaration, proof, import, manifest, test, or captured measurement.

## Environment

| Item | Value |
| --- | --- |
| Platform | Windows 11 |
| Lean toolchain | `leanprover/lean4:v4.29.0-rc3` |
| Mathlib revision | `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b` |
| Production target | `NumStability` |
| Test driver | `NumStabilityTest` |

## Migration result

The three historical owners now have semantic homes:

- `Source.Higham.Chapter14.Problem14` owns the Hyman-determinant source
  development;
- `Source.Higham.Chapter21.Theorem03.Attainment` owns the corrected
  Theorem-21.3 attainment and obstruction development; and
- `Analysis.Probability.Haar.HomogeneousSpaceUniqueness` owns the generic
  invariant-probability uniqueness API.

`Source.Higham.Chapter21.Theorem03` and `Analysis.Probability.Haar` are
declaration-free family aggregates. The historical
`Algorithms.Ch14HymanDeterminant`,
`Algorithms.Underdetermined.Higham21Theorem21_3Attainment`, and
`Algorithms.TestMatrices.Higham28HaarFibers` paths are one-import compatibility
wrappers. Production consumers use only canonical paths; isolated old-only
tests continue to verify each historical import surface.

The migration adds five production modules and eight isolated one-import tests.
The existing Chapter 14, Chapter 21, Probability, Algorithms, Source, All, and
root smokes exercise the new public surfaces.

## Exact compiled ownership and dependency preservation

The Phase 10D and refreshed Phase 10E dependency streams were compared after
normalizing only the three mapped module owners and the generated private
prefix belonging to the Hyman owner. The complete declaration records and both
dependency-edge sets match exactly.

| Canonical owner | Total | Public | Internal | Private | Signature edges | Body/proof edges |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Source.Higham.Chapter14.Problem14` | 39 | 12 | 24 | 3 | 49 | 124 |
| `Source.Higham.Chapter21.Theorem03.Attainment` | 29 | 18 | 11 | 0 | 76 | 144 |
| `Analysis.Probability.Haar.HomogeneousSpaceUniqueness` | 4 | 3 | 1 | 0 | 0 | 1 |

The family total is 72 compiled constants: 33 public, 36 generated internal,
and three private. The comparator checked the exact declaration name set, kind
and visibility per name, expected owner per name, and every signature and
body/proof edge. The global graph remains exactly 81,950 declarations, 305,425
signature edges, 439,195 body/proof edges, and 491,557 union edges.

## Immutable-map conformance

There is no implementation departure from the mapped production tree,
declaration ownership, wrapper surface, aggregate surface, consumer rewrites,
or test plan.

The frozen map calls the Haar result a finite homogeneous-space theorem. That
word is a prose imprecision: the declarations require transitivity and
invariant probability measures but no `Fintype` assumption. Live API
documentation and this evidence use the accurate description. This correction
does not alter the mapped destination or any declaration.

The map also compresses the three incoming Haar declaration edges as being
through `Higham28OrthogonalSphere`. Their actual declaring modules are
`Higham28OrthogonalFibers`, `Higham28OrthogonalCoordinates`, and
`Higham28StewartRawFiber`; they are downstream of
`Higham28OrthogonalSphere`, which remains the sole direct module importer. This
is likewise a prose correction, not an ownership or graph departure.

## Candidate-worktree Lean validation

| Command or gate | Result |
| --- | --- |
| Focused production frontier build | passed; 3,200 jobs |
| Canonical Chapter 14 Problem 14 build | passed; 3,079 jobs |
| Eight isolated canonical, aggregate, and wrapper tests | passed; 3,093 jobs |
| Seven affected entry-point smokes | passed; 4,788 jobs |
| `lake build NumStability` | passed; 4,782 jobs |
| `lake test` | passed; 5,219 jobs |
| `lake build NumStability NumStabilityTest` | passed; 5,221 jobs |
| `lake env lean examples/LibraryLookup.lean` | passed |
| Compiled declaration-graph extraction | passed |
| Exact old-versus-new metadata, ownership, and edge comparison | passed: exact 72-to-72 match |
| Strict-source baseline generation | passed |

These were cache-preserving validation builds. Existing Lean linter and
deprecation warnings remained visible; no error was hidden or waived.

## Architecture baseline

| Measure | Result |
| --- | ---: |
| Lean modules | 982 |
| Source lines | 1,468,334 |
| Nonblank source lines | 1,402,126 |
| Direct imports | 4,048 |
| Internal import edges | 2,680 |
| External imports | 1,368 |
| Import cycles | 0 |
| Classified modules | 370 |
| Classification coverage | 37.678% |
| Mixed modules | 0 |
| Uniquely owned declarations | 81,950 |
| Public declarations | 56,187 |
| Signature edges | 305,425 |
| Body/proof edges | 439,195 |
| Union edges | 491,557 |

The reviewed roles comprise 72 aggregates, 100 compatibility wrappers, two
internal modules, 57 reusable modules, 134 source modules, five upstream
modules, and zero reviewed mixed modules. There are zero direct or transitive
reusable-to-source or reusable-to-mixed paths.

Phase 10E reduces the unclassified inventory from 615 to 612, the missing
module-doc inventory from 219 to 218, and historical naming exceptions from 409
to 406. The compiled declaration and dependency graph remains exactly unchanged
from Phase 10D.

## Static validation

| Gate | Result |
| --- | --- |
| Layout, placeholder, test-reachability, and exact legacy-debt contract | passed: 982 modules |
| Classified source boundary | passed: zero forbidden direct or reachable paths |
| Compatibility contract | passed: 100 wrappers, 199 direct targets |
| Provenance contract | passed: 207 Apache files, five upstream modules |
| Aggregate structural and ordering contract | passed: 72 classified aggregates |
| Declaration-bearing umbrellas | passed: zero |
| Unsorted classified aggregates | passed: zero |
| Baseline reproducibility comparison | passed |
| Independent production review | passed: no unresolved findings |
| Independent documentation review | passed after corrections |
| Independent frozen full-diff review | passed: no findings |
| `git diff --check` | passed |

The remaining exact debt is 612 unclassified modules, 218 missing module
docstrings, and 406 historical naming exceptions. Partial classification means
that the zero mixed count is a ratchet, not a claim that every remaining
historical module is already semantically pure.

## Review corrections

Independent review found four documentation issues before the implementation
commit. All were corrected and the diff was frozen before final validation:

- the moved Problem 14 module no longer describes itself as import-only or
  reverses its relationship to `MatrixInversion`;
- live tier and endpoint documentation no longer calls the Haar theorem finite;
- Chapter 28 coverage now says that the three-theorem API supports the Stewart
  development instead of claiming that all three theorems have external
  consumers; and
- endpoint documentation names the three actual incoming declaration-edge
  sources while retaining `Higham28OrthogonalSphere` as the sole direct module
  importer.

The production and final full-diff reviews then reported no actionable
findings. They independently checked moved declaration bodies, normalized graph
records, wrappers, aggregates, isolated tests, canonical production consumers,
manifests, statistics, and whitespace.

## Clean-commit verification

The production tree at implementation revision
`eead3f9a3880055435b39ba7dbee95ec5225cba7` was clean before the architecture
pair was captured. The following gates were repeated from committed source:

| Command or gate | Result |
| --- | --- |
| Initial `git status --short` | passed: no output |
| `lake test` | passed; 5,219 jobs |
| `lake build NumStability NumStabilityTest` | passed; 5,221 jobs |
| `lake env lean examples/LibraryLookup.lean` | passed |
| Layout and exact legacy-debt contract | passed: 982 modules |
| Compatibility contract | passed: 100 wrappers, 199 direct targets |
| Provenance contract | passed: 207 Apache files, five upstream modules |
| Clean strict-source baseline capture | passed: 81,950 compiled declarations |
| Baseline `--check` against the retained dependency extraction | passed |

The generated baseline records `library_source_clean: true`, the implementation
revision, and source-tree digest
`ecf887859377fc8e794d2d4a714943a165bc6fa708b85553c96e50c60b886b9b`.

## Captured artifacts

- [Human-readable architecture baseline](2026-07-26-organization-phase10e.md)
- [Machine-readable architecture baseline](2026-07-26-organization-phase10e.json)
- [Phase 10E migration and ownership record](../migrations/2026-07-24-higham-frontiers-phase10e.md)

The source, import, declaration, toolchain, and Mathlib measurements were
reproduced before this evidence-only commit.
