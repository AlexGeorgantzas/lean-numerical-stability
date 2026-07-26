# Organization phase 10F build evidence (2026-07-26)

This record covers the semantic reorganization of the remaining audited
Higham frontiers in Chapters 14, 21, and 28: reusable Weyl--Mirsky singular
value bounds, Problem 14.15 determinant perturbation results, Theorem 21.4
rowwise backward error, and the equation (28.2) Hilbert-ratio discrepancy.

Development started from the pushed Phase 10E checkpoint
b43ef1e0dbc36c22f959fba757a8c97a6df55cf3 on
codex/organization-phase-10f-higham-frontiers. The immutable ownership map was
committed before implementation as
b9911b719d87436b3cd691d8ab6a0ee90cec9b10.

Candidate-worktree and clean-commit validation are recorded separately. The
implementation revision is
2bd764158903f1faa7eafc4e15006147adc287eb. The architecture pair was captured
from that clean revision and committed as
9567ebd1199b813c01d5317d6fad0af57a15832c. This evidence update changes no Lean
declaration, proof, import, manifest, test, or captured measurement.

## Environment

| Item | Value |
| --- | --- |
| Platform | Windows 11 |
| Lean toolchain | leanprover/lean4:v4.29.0-rc3 |
| Mathlib revision | e8ea1afc32790ce1d4e1a4e45cc412ba9388716b |
| Production target | NumStability |
| Test driver | NumStabilityTest |

## Migration result

The three historical owners now have four semantic homes:

- Analysis.SingularValues.WeylMirsky owns the reusable singular-value
  perturbation API;
- Source.Higham.Chapter14.Problem15 owns the source-specific determinant
  perturbation results;
- Source.Higham.Chapter21.Theorem04.RowwiseBackwardError owns the Theorem 21.4
  rowwise backward-error development; and
- Source.Higham.Chapter28.Equation02.RatioDiscrepancy owns the equation (28.2)
  Hilbert-ratio discrepancy.

Analysis.SingularValues, Source.Higham.Chapter21.Theorem04,
Source.Higham.Chapter28, and Source.Higham.Chapter28.Equation02 are
declaration-free aggregates. The historical
Algorithms.Chapter14Problem1415Weyl,
Algorithms.Underdetermined.Higham21RowwiseMeasure, and
Algorithms.TestMatrices.Higham28HilbertRatioDiscrepancy paths are one-import
compatibility wrappers. Production consumers use only canonical paths;
isolated old-only tests continue to verify each historical import surface.

The reusable Weyl--Mirsky leaf has no Algorithms dependency. Chapter 14
Problem 15 imports its reusable prerequisites explicitly. The Chapter 28 leaf
retains the documented dependency on
Algorithms.TestMatrices.Higham28HilbertAsymptotic because that historical
asymptotic development has not yet been semantically migrated.

The migration adds eight production modules and eleven isolated one-import
tests. Existing Analysis, Algorithms, Source, Higham, All, and root smokes
exercise the new public surfaces.

## Exact compiled ownership and dependency preservation

The Phase 10E and Phase 10F dependency streams were compared after normalizing
only the four mapped module owners and the two generated Chapter 14 private
prefixes. The complete declaration records and both dependency-edge sets match
exactly.

| Canonical owner | Total | Public | Internal | Private | Signature edges | Body/proof edges |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Analysis.SingularValues.WeylMirsky | 17 | 4 | 3 | 10 | 14 | 43 |
| Source.Higham.Chapter14.Problem15 | 10 | 7 | 0 | 3 | 24 | 48 |
| Source.Higham.Chapter21.Theorem04.RowwiseBackwardError | 19 | 18 | 1 | 0 | 48 | 66 |
| Source.Higham.Chapter28.Equation02.RatioDiscrepancy | 27 | 11 | 16 | 0 | 11 | 39 |

The moved family contains 73 compiled constants: 40 public, 20 generated
internal, and 13 private. The comparator checked the exact declaration name
set, kind and visibility per name, expected owner per name, and every signature
and body/proof edge. The global graph remains exactly 81,950 declarations,
305,425 signature edges, 439,195 body/proof edges, and 491,557 union edges.

The raw Phase 10E TSV has SHA-256
03BC2291A655E9AC394966B6C435E0A25E74B0A56E6EFEEACCDC606C1E8FDE18.
The raw Phase 10F TSV has SHA-256
958CB3FFB9A7814A80B33E31B1A162E7F2E4E630FE025A48EA6330EC8438BF93.
After mapped normalization, the order-independent multisets differ by zero
missing and zero extra records, with duplicate multiplicity preserved.

## Immutable-map conformance

There is no semantic or ownership departure from the mapped production tree,
declaration ownership, wrapper surface, aggregate surface, consumer rewrites,
or test plan. There are two direct-import deviations from the map's frozen
exact-change prose, plus one forecast arithmetic correction; all three are
listed below.

The immutable map forecast 4,060 direct imports, split into 2,692 internal and
1,368 external imports. The measured result is 4,063 direct imports, split
into 2,694 internal and 1,369 external imports. The three-edge difference is
fully accounted for:

- WeylMirsky explicitly imports
  Mathlib.Analysis.CStarAlgebra.Module.Constructions for an instance that was
  previously available transitively;
- Higham20Lemma20_11 explicitly imports
  Algorithms.LeastSquares.LSPerturbation after removal of its stale transitive
  MatrixInversion route; and
- the map's base arithmetic undercounted the planned internal-import delta by
  one.

The immutable record remains unchanged as the pre-edit forecast. Live
documentation and the captured baseline use the audited measurements.

## Candidate-worktree Lean validation

| Command or gate | Result |
| --- | --- |
| Chapter 14 focused frontier build | passed; 3,099 jobs |
| Chapter 21 focused frontier build | passed; 3,116 jobs |
| Chapter 28 focused frontier build | passed; 2,793 jobs |
| Eleven isolated canonical, aggregate, and wrapper tests | passed |
| lake build NumStability NumStabilityTest | passed; 5,240 jobs |
| lake test | passed; 5,238 jobs |
| lake env lean examples/LibraryLookup.lean | passed |
| Compiled declaration-graph extraction | passed |
| Exact old-versus-new metadata, ownership, and edge comparison | passed: exact 73-to-73 match |
| Strict-source baseline generation | passed |

These were cache-preserving validation builds. Existing Lean linter and
deprecation warnings remained visible; no error was hidden or waived.

## Architecture baseline

| Measure | Result |
| --- | ---: |
| Lean modules | 990 |
| Source lines | 1,468,408 |
| Nonblank source lines | 1,402,180 |
| Direct imports | 4,063 |
| Internal import edges | 2,694 |
| External imports | 1,369 |
| Import cycles | 0 |
| Classified modules | 381 |
| Classification coverage | 38.485% |
| Mixed modules | 0 |
| Uniquely owned declarations | 81,950 |
| Public declarations | 56,187 |
| Signature edges | 305,425 |
| Body/proof edges | 439,195 |
| Union edges | 491,557 |

The reviewed roles comprise 76 aggregates, 103 compatibility wrappers, two
internal modules, 58 reusable modules, 137 source modules, five upstream
modules, and zero reviewed mixed modules. There are zero direct or transitive
reusable-to-source or reusable-to-mixed paths.

Phase 10F reduces the unclassified inventory from 612 to 609, the missing
module-doc inventory from 218 to 217, and historical naming exceptions from
406 to 403. The compiled declaration and dependency graph remains exactly
unchanged from Phase 10E.

## Static validation

| Gate | Result |
| --- | --- |
| Layout, placeholder, test-reachability, and exact legacy-debt contract | passed: 990 modules |
| Classified source boundary | passed: zero forbidden direct or reachable paths |
| Compatibility contract | passed: 103 wrappers, 202 direct targets |
| Provenance contract | passed: 207 Apache files, five upstream modules |
| Aggregate structural and ordering contract | passed: 76 classified aggregates |
| Declaration-bearing umbrellas | passed: zero |
| Unsorted classified aggregates | passed: zero |
| Baseline reproducibility comparison | passed |
| Independent frozen full-diff review | passed: no unresolved findings |
| git diff --check | passed |

The remaining exact debt is 609 unclassified modules, 217 missing module
docstrings, and 403 historical naming exceptions. Partial classification means
that the zero mixed count is a ratchet, not a claim that every remaining
historical module is already semantically pure.

## Review corrections

Independent review found two import-order issues and one stale documentation
measurement set before the implementation commit. Both import blocks were
sorted, and live documentation was corrected from the immutable forecast to
the measured 4,063 / 2,694 / 1,369 import counts.

The final review then reported no actionable findings. It independently
checked moved declaration bodies, normalized graph records, wrappers,
aggregates, isolated tests, canonical production consumers, manifests,
statistics, documentation, and whitespace.

## Clean-commit verification

The production tree at implementation revision
2bd764158903f1faa7eafc4e15006147adc287eb was clean before the architecture
pair was captured. The following gates were repeated from committed source:

| Command or gate | Result |
| --- | --- |
| Initial git status --short | passed: no output |
| Focused leaves, aggregates, wrappers, consumers, and eleven isolated tests | passed; 4,729 jobs |
| lake build NumStability | passed; 4,787 jobs |
| lake build NumStability NumStabilityTest | passed; 5,240 jobs |
| lake test | passed; 5,238 jobs |
| lake env lean examples/LibraryLookup.lean | passed |
| Layout and exact legacy-debt contract | passed: 990 modules |
| Compatibility contract | passed: 103 wrappers, 202 direct targets |
| Provenance contract | passed: 207 Apache files, five upstream modules |
| Fresh clean-source declaration/dependency extraction | passed: 81,950 compiled declarations |
| Exact normalized Phase 10E/10F graph comparison | passed: zero missing and zero extra records |
| Clean strict-source baseline capture and reproducibility check | passed |

The generated baseline records library_source_clean: true, the implementation
revision, and source-tree digest
1d9e1f241fe7dac8113f16c6230e92df39f02f28e8a2e5e764d6ae4005f76381.

## Captured artifacts

- [Human-readable architecture baseline](2026-07-26-organization-phase10f.md)
- [Machine-readable architecture baseline](2026-07-26-organization-phase10f.json)
- [Phase 10F migration and ownership record](../migrations/2026-07-26-higham-source-frontiers-phase10f.md)

The source, import, declaration, toolchain, and Mathlib measurements were
reproduced before this evidence-only commit.
