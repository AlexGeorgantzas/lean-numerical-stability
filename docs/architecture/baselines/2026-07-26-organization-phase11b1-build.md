# Organization Phase 11B1 build evidence (2026-07-26)

This record covers the bounded semantic split of the 1,783-constant
`Analysis.Norms.Core` implementation. Twenty reusable analysis leaves now own
the generic norm, operator, singular-value, conditioning, and asymptotic APIs.
Four canonical `Source.Higham.Chapter06` problem leaves own the source-shaped
Chapter 6 results. `Analysis.Norms.Core` is now a declaration-free aggregate,
while `Analysis.Norms` remains the historical compatibility facade.

Development started from the pushed Phase 11A evidence revision
`66e2451d005e380c69015e525dc9b3e33ce95194`. The immutable ownership map was
committed before implementation as
`60d0bb7e9d8e5fab3970144a4f045a4bbd38133d`.

Candidate-worktree and clean-commit validation are recorded separately. The
implementation revision is
`27a96739a6f7027cd104297fc29e4730f156b8c8`. The architecture pair was
captured from that clean revision and committed as
`5041fea06948b5f8f9436c9d338b34bfc66b626e`. This evidence update changes no
Lean declaration, proof, import, manifest, test, or captured measurement.

## Environment

| Item | Value |
| --- | --- |
| Platform | Windows 11 |
| Lean toolchain | leanprover/lean4:v4.29.0-rc3 |
| Mathlib revision | e8ea1afc32790ce1d4e1a4e45cc412ba9388716b |
| Production target | NumStability |
| Test driver | NumStabilityTest |

## Migration result

The transitional 23,631-line Core was replaced by a semantic hierarchy:

- `Analysis.VectorNorms`, `LinearOperators`, `OperatorNorms`, `MatrixNorms`,
  `SingularValues`, `Conditioning`, and `Asymptotics` expose the reusable
  families through focused declaration-bearing leaves and sorted,
  declaration-free umbrellas;
- `Source.Higham.Chapter06.Problem01`, `Problem05`, `Problem09`, and
  `Problem10` own the source-shaped closures, with `Chapter06.Norms` as their
  bounded source aggregate;
- `Analysis.Norms.Core` imports exactly the reusable surface and declares
  nothing;
- `Analysis.Norms` forwards to Core plus the bounded Chapter 6 norms
  aggregate; and
- the stale Core dependency in `Source.Higham.Chapter23.BilinearAlgorithm`
  was replaced by its two actual Mathlib imports.

All 23 direct Core consumers were retargeted to their narrow semantic owners.
Thirty-one new isolated one-import tests cover every new canonical leaf and
umbrella; the existing Core, historical-facade, Chapter 6, Analysis, Source,
Higham, All, and root smokes were strengthened to cover the new surfaces.

Phase 11B1 intentionally does not relocate the 69 constants still owned by
`Algorithms.Chapter06Lemma66`, `Analysis.Higham6Asides`,
`Analysis.Higham6BlockAntidiag`, and `Analysis.HighamChapter6Duality`. Those
four source moves, wrappers, and isolated tests are the separately mapped
Phase 11B2 completion gate.

## Exact compiled ownership and dependency preservation

| Destination class | Owners | Total | Public | Internal | Private |
| --- | ---: | ---: | ---: | ---: | ---: |
| Reusable analysis leaves | 20 | 1,624 | 1,254 | 369 | 1 |
| Chapter 6 source leaves | 4 | 159 | 131 | 25 | 3 |
| **Moved Core family** | **24** | **1,783** | **1,385** | **394** | **4** |

The tracked ownership manifest maps every compiled constant to one exact
destination, including generated internal and private declarations. The
post-migration checker confirms exact owner, logical name, kind, visibility,
and multiplicity, then normalizes the 24 destinations back to the Phase 11A
Core owner and compares the entire declaration and edge streams.

The normalized comparison reports zero missing and zero extra records. The
global graph remains exactly 81,950 declarations, 305,425 signature edges,
439,195 body/proof edges, and 491,557 union edges. The raw Phase 11A TSV has
SHA-256
`7FFBDD7F54F4DD19C0FCD5962D41A01A09ED55F6E251DB7F4240B42D340E6A09`.
The raw Phase 11B1 TSV has SHA-256
`89A22BFBB70513DE4FEE3734AABC1FDADA3FC7C737164923808CBCD4FC79EB30`.

## Immutable-map conformance

The implementation matches all 24 destination assignments and the frozen
29-edge owner DAG. The 18,895 incident edges comprise 7,403 signature and
11,492 body/proof edges; all 12,625 edges internal to the partition are
preserved. The owner graph is acyclic and has no reusable-to-source path.

The structural forecast is exact: 1,024 production modules, 416 classified
modules, 608 unclassified modules, 85 aggregates, 104 compatibility modules,
78 reusable modules, 142 source modules, two internal modules, five upstream
modules, and zero reviewed mixed modules. Compatibility remains 104 wrappers
with 204 direct targets. Missing module documentation remains 217 and the
historical naming-exception ratchet remains 403.

External Mathlib imports were minimized during isolated compilation, as the
map permits. The measured direct-import graph has 4,134 edges: 2,774 internal
and 1,360 external. There are no unresolved project imports or import cycles.

## Candidate-worktree Lean validation

| Command or gate | Result |
| --- | --- |
| Focused leaf, umbrella, source, consumer, and import-test builds | passed |
| `lake build NumStability` | passed; 4,819 jobs |
| `lake test` | passed; 5,307 jobs |
| `lake build NumStability NumStabilityTest` | passed; 5,309 jobs |
| `lake env lean examples/LibraryLookup.lean` | passed |
| Twenty-four-owner representative axiom audit | passed; exactly `propext`, `Classical.choice`, and `Quot.sound` |
| Exact normalized Phase 11A/11B1 graph comparison | passed: 1,783 constants and the full graph preserved |
| Strict-source architecture capture and check | passed |

The first text validator for the axiom audit treated Lean's wrapped dependency
lists as unparsed single lines. The Lean audit itself had succeeded; a
multi-line validator was run immediately and confirmed all 24 results against
the allowed set with no additional axiom.

## Architecture baseline

| Measure | Result |
| --- | ---: |
| Lean modules | 1,024 |
| Source lines | 1,469,113 |
| Nonblank source lines | 1,402,702 |
| Direct imports | 4,134 |
| Internal import edges | 2,774 |
| External imports | 1,360 |
| Import cycles | 0 |
| Classified modules | 416 |
| Classification coverage | 40.625% |
| Mixed modules | 0 |
| Uniquely owned declarations | 81,950 |
| Public declarations | 56,187 |
| Signature edges | 305,425 |
| Body/proof edges | 439,195 |
| Union edges | 491,557 |

The reviewed roles have zero direct or transitive reusable-to-source or
reusable-to-mixed paths. Classification is still incomplete, so the zero
mixed count is a ratchet over reviewed modules rather than a claim that the
608-module unclassified corpus is source-pure.

## Static validation

| Gate | Result |
| --- | --- |
| Layout, placeholder, test-reachability, and exact legacy-debt contract | passed: 1,024 modules |
| Classified source boundary | passed: zero forbidden direct or reachable paths |
| Compatibility contract | passed: 104 wrappers, 204 direct targets |
| Provenance contract | passed: 207 Apache files, five upstream modules |
| Aggregate structural and ordering contract | passed: 85 classified aggregates |
| Declaration-bearing umbrellas | passed: zero |
| Unsorted classified aggregates | passed: zero |
| Ownership manifest and frozen owner DAG | passed: 24 owners, exact 29-edge DAG |
| Baseline reproducibility with retained and freshly extracted TSVs | passed |
| Independent production, test, map, and documentation review | passed after corrections |
| `git diff --check` | passed |

## Review corrections

Independent review confirmed the source partition, direct-consumer retargets,
aggregate surfaces, compatibility targets, isolated tests, and full graph
comparison. It also found two stale review statements: the physical-target
decision still listed Norms as an unresolved mixed owner, and the summation
review still reported one mixed module. The live documents now record that
Norms is resolved in Phase 11B1 and the reviewed summation mixed queue is zero.

Moving the declarations changed Lean's generated-helper allocation order even
though the named source commands were preserved mechanically. Nine local
counter resets, nine lazy owner materializations, and four tightly scoped
reuses of frozen local instances were required to retain the exact generated
declaration ABI under the pinned toolchain. Each adjustment was kept at the
narrowest declaration scope. The final full-stream comparison proves that no
named or generated declaration, signature edge, or body/proof edge drifted.

## Clean-commit verification

The production tree at implementation revision
`27a96739a6f7027cd104297fc29e4730f156b8c8` was clean before the declaration
stream and architecture pair were regenerated. The following gates were
repeated from committed source:

| Command or gate | Result |
| --- | --- |
| Initial `git status --short` | passed: no output |
| Fresh declaration/dependency extraction | passed: 131,967,513-byte TSV |
| Exact normalized Phase 11A/11B1 graph comparison | passed: zero missing and zero extra records |
| Clean named architecture baseline capture | passed |
| Reproduction from retained declaration TSV | passed |
| Independent reproduction from current compiled environment | passed |
| Strict-source baseline capture and check | passed |
| Layout, compatibility, and provenance contracts | passed |
| `lake build NumStability` | passed; 4,819 jobs |
| `lake test` | passed; 5,307 jobs |
| `lake build NumStability NumStabilityTest` | passed; 5,309 jobs |
| `lake env lean examples/LibraryLookup.lean` | passed |
| Representative axiom audit | passed at the established ceiling |

The generated baseline records `library_source_clean: true`, implementation
revision `27a96739a6f7027cd104297fc29e4730f156b8c8`, and normalized source-tree
digest `549699a3f5dc26436fe81a4d2cce8071ae1f946c13a8bf500833cc6547214907`.

## Captured artifacts

- [Human-readable architecture baseline](2026-07-26-organization-phase11b1.md)
- [Machine-readable architecture baseline](2026-07-26-organization-phase11b1.json)
- [Phase 11B1 immutable migration and ownership record](../migrations/2026-07-26-analysis-norms-semantic-phase11b1.md)
- [Phase 11B1 declaration-ownership manifest](../declaration-ownership/norms-phase11b1.tsv)

The source, import, declaration, toolchain, Mathlib, ownership, and axiom
measurements were reproduced before this evidence-only commit.
