# Organization phase 4 build evidence (2026-07-24)

This evidence covers the compensated-summation migration developed on
`codex/organization-phase-4` from
`312a970cddfb5c41da81237bb34b5cb5fd0c93e4`. The checks ran against the
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

The former compensated-summation monolith is now a declaration-free complete
aggregate over reusable correction-formula, FastTwoSum, Kahan, Alternative,
no-guard, and finite-format families plus the Chapter 4 source correspondence
that its historical import exposed. The old finite-format path is an
import-only compatibility wrapper. All newly introduced family, equation, and
section umbrellas are documented and declaration-free.

The final exact-surface audit elaborated all 690 named public declarations and
the named public `kahanSameSignDecidable` instance from the old compensated
module through the new aggregate. It also elaborated all 14 declarations from
the old finite-format module. Seven private proof helpers were correctly
excluded from compatibility requirements. Extracted declaration bodies match
their pre-migration owners after newline normalization.

## Lean validation

| Command or gate | Result |
| --- | --- |
| Isolated reusable and source leaf builds | passed |
| Canonical finite-format leaves and curated section surface | passed; 1,498 jobs |
| Finite-format consumers, old wrapper, and isolated smokes | passed; 3,493 jobs |
| Restored complete-aggregate compatibility smokes | passed; 3,196 jobs |
| `lake test` | passed; 4,864 of 4,864 jobs built |
| `lake build NumStability NumStabilityTest` | passed; 4,866 jobs built |
| Full architecture-baseline production build | passed; 4,697 jobs built |
| Compiled declaration extraction | passed |
| Baseline reproducibility check | passed |

The broad aggregate test initially caught two absent historical re-exports,
`kahanFF_kahanSum_backward_error` and
`kahanFF_kahanSum_forward_error`. Importing the canonical declaration-free
`Source.Higham.Chapter04.Section03.FiniteFormat` surface from the complete
compensated aggregate fixed the regression without contaminating either
reusable finite-format leaf with a source dependency.

These were cache-preserving validation builds. Existing Lean linter and
deprecation warnings remain visible; no error was hidden or waived.

## Architecture baseline

| Measure | Result |
| --- | ---: |
| Lean modules | 831 |
| Source lines | 1,466,261 |
| Direct imports | 3,638 |
| Import cycles | 0 |
| Classified modules | 181 |
| Classification coverage | 21.781% |
| Mixed modules | 0 |
| Uniquely owned declarations | 81,925 |
| Public declarations | 56,187 |
| Signature edges | 305,418 |
| Body/proof edges | 439,180 |

Phase 4 increases the reviewed inventory while reducing the known mixed queue
from one module to zero. The physical source-target gate remains intentionally
false because 650 modules have not yet been classified. Within the reviewed
graph there are zero direct or transitive reusable-to-source or
reusable-to-mixed paths.

## Static validation

| Gate | Result |
| --- | --- |
| Layout contract | passed: 831 modules |
| Exact legacy-debt ratchet | passed |
| Classified source boundary | passed: zero forbidden direct or reachable paths |
| Compatibility contract | passed: 46 wrappers, 47 canonical targets |
| Provenance contract | passed: 148 Apache files, 5 upstream modules |
| Aggregate ordering | passed for every classified aggregate |
| Strict-source baseline | passed |
| Apache normalization dry run | passed: zero files require changes |
| Architecture Python syntax validation | passed |
| Architecture JSON validation | passed |
| `git diff --check` | passed |

The aggregate sorter was also corrected to examine only the initial Lean
import block. Documentation prose beginning with the word `import` can no
longer produce a false noncontiguous-import failure. A focused regression
sample and a read-only pass over every classified aggregate both succeed.

The remaining exact debt is 650 unclassified modules, 227 missing module
docstrings, 454 historical naming exceptions, and the one reviewed legacy
declaration-bearing `FastMatMul` umbrella. There are no mixed modules and no
unsorted aggregates.

## Captured artifacts

- [Human-readable architecture baseline](2026-07-24-organization-phase4.md)
- [Machine-readable architecture baseline](2026-07-24-organization-phase4.json)
- [Phase 4A migration record](../migrations/2026-07-23-compensated-phase4a.md)
- [Phase 4B migration record](../migrations/2026-07-23-compensated-phase4b.md)
- [Phase 4C migration record](../migrations/2026-07-23-compensated-phase4c-kahan.md)
- [Phase 4D migration record](../migrations/2026-07-23-compensated-phase4d-variants.md)

The baseline records the exact dirty production paths included in this
candidate capture. A final clean-checkout verification belongs to the
repository-wide release gate after the remaining organization phases.
