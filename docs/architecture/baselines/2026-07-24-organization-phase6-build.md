# Organization phase 6 build evidence (2026-07-24)

This evidence covers the Higham source-endpoint migration developed on
`codex/organization-phase-6-source-endpoints` from
`1a35c73595be2a3fff7715cfd7a1e9316ca3bb83`. The checks ran against the
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

Six declaration-bearing historical modules covering Higham Chapters 04, 17,
and 26 are now documented, direct, import-only compatibility wrappers. Their
246 public declarations and five private proof helpers moved into 33 canonical
source leaves under `NumStability.Source.Higham`. Eight declaration-free
chapter or family aggregates provide the semantic import surface, for 41 new
canonical production modules in total.

All 246 public declarations retain their names and unique production
ownership. Normalized implementation-body comparisons against the frozen
pre-migration owners passed for every declaration, including the five private
Chapter 26 helpers. The chapter audits covered 61 public Chapter 04
declarations, 44 public Chapter 17 declarations, and 141 public plus five
private Chapter 26 declarations. No production module imports any of the six
historical implementation paths after this batch.

The historical `Algorithms` discovery aggregate preserves its prior surface
through canonical chapter imports. `Analysis`, `Source.Higham`, the root import
smokes, and the library-lookup example now use the canonical endpoints. The 47
new isolation tests cover every canonical leaf and aggregate and all six
old-only compatibility imports.

## Lean validation

| Command or gate | Result |
| --- | --- |
| Chapter 04 canonical modules, wrappers, and five isolated tests | passed |
| Chapter 17 canonical modules, wrappers, and 11 isolated tests | passed |
| Chapter 26 canonical modules, wrappers, and 31 isolated tests | passed; 3,225 jobs |
| Ten broad entry-point import smokes | passed |
| `examples/LibraryLookup.lean` elaboration | passed |
| `lake test` | passed; 5,026 of 5,026 jobs built |
| `lake build NumStability NumStabilityTest` | passed; 5,028 jobs built |
| Full architecture-baseline production build | passed; 4,746 jobs built |
| Compiled declaration extraction | passed |
| Baseline reproducibility check | passed |

These were cache-preserving validation builds. Existing Lean linter and
deprecation warnings remain visible; no error was hidden or waived.

## Architecture baseline

| Measure | Result |
| --- | ---: |
| Lean modules | 898 |
| Source lines | 1,467,171 |
| Direct imports | 3,801 |
| Import cycles | 0 |
| Classified modules | 254 |
| Classification coverage | 28.285% |
| Mixed modules | 0 |
| Uniquely owned declarations | 81,933 |
| Public declarations | 56,187 |
| Signature edges | 305,418 |
| Body/proof edges | 439,182 |

The public declaration population and signature-edge count are identical to
Phase 5, as required for a pure ownership and import migration. The eight new
internal theorems are Lean-generated `_proof_n` constants for numeral
`AtLeastTwo` instances: splitting the Chapter 26 monolith resets per-module
sharing and materializes the same synthesized side conditions in their new
leaves. The two extra body/proof edges are the corresponding duplicated local
proof references in `stableCubicWCube_eq_branch` and
`stableCubicWCubeComplex_eq_branch`. No explicit declaration, public/private
API, normalized body, or signature dependency changed. Phase 6 classifies all
41 new canonical modules and the six historical wrappers, reducing the
unclassified inventory by six. Within the reviewed graph there are zero direct
or transitive reusable-to-source or reusable-to-mixed paths.

## Static validation

| Gate | Result |
| --- | --- |
| Layout contract | passed: 898 modules |
| Exact legacy-debt ratchet | passed |
| Classified source boundary | passed: zero forbidden direct or reachable paths |
| Compatibility contract | passed: 64 wrappers, 97 canonical targets |
| Provenance contract | passed: 177 Apache files, 5 upstream modules |
| Aggregate ordering | passed for every classified aggregate |
| Strict-source baseline | passed |
| Apache normalization dry run | passed: zero files require changes |
| Architecture JSON validation | passed |
| `git diff --check` | passed |

The remaining exact debt is 644 unclassified modules, 225 missing module
docstrings, 437 historical naming exceptions, and the one reviewed legacy
declaration-bearing `FastMatMul` umbrella. There are no mixed modules and no
unsorted aggregates.

## Captured artifacts

- [Human-readable architecture baseline](2026-07-24-organization-phase6.md)
- [Machine-readable architecture baseline](2026-07-24-organization-phase6.json)
- [Phase 6 migration record](../migrations/2026-07-24-higham-source-endpoints-phase6.md)

The baseline records the exact dirty production paths included in this
candidate capture. A final clean-checkout verification belongs to the
repository-wide release gate after the remaining organization phases.
