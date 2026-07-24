# Organization phase 5 build evidence (2026-07-24)

This evidence covers the canonical Higham-path migration developed on
`codex/organization-phase-5-higham` from
`b955d485096416758d81c2b72301396e6bf18ab1`. The checks ran against the
candidate worktree before commit; the implementation revision is the commit
containing this record.

## Environment

| Item | Value |
| --- | --- |
| Platform | Windows 11 |
| Lean toolchain | `leanprover/lean4:v4.29.0-rc3` |
| Mathlib revision | `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b` |
| Production target | `NumStability` |
| Test driver | `NumStabilityTest` |

The Mathlib dependency is pinned to the exact revision above in the Lake
configuration and lock file.

## Migration result

The twelve declaration-bearing modules below `NumStability.Higham` that were
still acting as implementation owners are now documented import-only
compatibility wrappers. Their 81 public declarations and 22 private proof
helpers moved to canonical Chapter 02, 08, 10, 11, 13, and 20 source leaves,
semantic cross-chapter source leaves, or the reusable no-guard dot-product
family. The twelve still older `Analysis` and `Algorithms` forwarding paths
now import the final owners directly rather than forming wrapper chains.

All 81 public declarations retain their names and unique production ownership.
Normalized implementation-body comparisons against the pre-migration owners
passed, including the complete 22-helper private Chapter 10 cluster. The
no-guard split separately verified the exact 9-declaration reusable core,
4-declaration tree layer, and 4 numbered source endpoints. No production
module imports a `NumStability.Higham.*` compatibility path after this batch.

The canonical root now exposes declaration-free chapter umbrellas for all
chapters touched by this migration and a semantic `CrossChapter` tree. This is
an incremental source migration: the remaining historical Higham corpus still
requires dependency-contained review and is not represented as complete.

## Lean validation

| Command or gate | Result |
| --- | --- |
| Chapter 02 canonical, wrapper, consumer, and isolated-smoke build | passed; 1,498 jobs |
| Chapters 08, 10, and 11 canonical leaves | passed; 3,083 jobs |
| Chapters 08, 10, and 11 umbrellas, wrappers, consumer, and smokes | passed; 3,105 jobs |
| Chapters 13 and 20 canonical leaves and umbrellas | passed; 3,082 jobs |
| Chapters 13 and 20 wrappers and isolated smokes | passed; 3,097 jobs |
| Cross-chapter canonical leaves | passed; 3,371 jobs |
| Cross-chapter aggregates and eight wrappers | passed; 3,382 jobs |
| Cross-chapter isolated smokes | passed; 3,399 jobs |
| Normalized Chapter 02/08/10/11/13/20 smoke layout | passed; 3,180 jobs |
| `NumStability.Source.Higham` | passed; 3,535 jobs |
| `lake test` | passed; 4,938 of 4,938 jobs built |
| `lake build NumStability NumStabilityTest` | passed; 4,940 jobs built |
| Full architecture-baseline production build | passed; 4,711 jobs built |
| Compiled declaration extraction | passed |
| Baseline reproducibility check | passed |

These were cache-preserving validation builds. Existing Lean linter and
deprecation warnings remain visible; no error was hidden or waived.

## Architecture baseline

| Measure | Result |
| --- | ---: |
| Lean modules | 857 |
| Source lines | 1,466,496 |
| Direct imports | 3,680 |
| Import cycles | 0 |
| Classified modules | 207 |
| Classification coverage | 24.154% |
| Mixed modules | 0 |
| Uniquely owned declarations | 81,925 |
| Public declarations | 56,187 |
| Signature edges | 305,418 |
| Body/proof edges | 439,180 |

The declaration population and dependency-edge counts are identical to Phase
4, as required for a pure ownership and import migration. Phase 5 adds 26
classified production modules while leaving the unclassified inventory fixed.
Within the reviewed graph there are zero direct or transitive reusable-to-
source or reusable-to-mixed paths.

## Static validation

| Gate | Result |
| --- | --- |
| Layout contract | passed: 857 modules |
| Exact legacy-debt ratchet | passed |
| Classified source boundary | passed: zero forbidden direct or reachable paths |
| Compatibility contract | passed: 58 wrappers, 67 canonical targets |
| Provenance contract | passed: 148 Apache files, 5 upstream modules |
| Aggregate ordering | passed for every classified aggregate |
| Strict-source baseline | passed |
| Apache normalization dry run | passed: zero files require changes |
| Architecture JSON validation | passed |
| `git diff --check` | passed |

The remaining exact debt is 650 unclassified modules, 227 missing module
docstrings, 442 historical naming exceptions, and the one reviewed legacy
declaration-bearing `FastMatMul` umbrella. There are no mixed modules and no
unsorted aggregates.

## Captured artifacts

- [Human-readable architecture baseline](2026-07-24-organization-phase5.md)
- [Machine-readable architecture baseline](2026-07-24-organization-phase5.json)
- [Phase 5 migration record](../migrations/2026-07-24-higham-canonical-phase5.md)

The baseline records the exact dirty production paths included in this
candidate capture. A final clean-checkout verification belongs to the
repository-wide release gate after the remaining organization phases.
