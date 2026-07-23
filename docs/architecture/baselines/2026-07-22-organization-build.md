# Organization phase 1 build evidence (2026-07-22)

This evidence covers the candidate worktree developed on
`codex/organize-repository` from
`11a5241c7496851a8653080f30d39182c4eeb4d4`. The checks ran before the
candidate was committed; the implementation revision is the commit containing
this record.

## Environment

| Item | Value |
| --- | --- |
| Platform | Windows 11 |
| Lean toolchain | `leanprover/lean4:v4.29.0-rc3` |
| Mathlib revision | `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b` |
| Production target | `NumStability` |
| Test driver | `NumStabilityTest` |

The Mathlib dependency is pinned to the exact revision above in both the Lake
configuration and lock file.

## Lean validation

| Command or gate | Result |
| --- | --- |
| `lake test` | passed; 4,741 of 4,741 jobs built |
| Full architecture-baseline build | passed; 4,641 jobs built |
| Compiled declaration extraction | passed |

`lake test` covers the production root, curated and complete entry points,
source and historical entry points, family umbrellas, canonical-only imports,
and isolated compatibility imports. The full baseline records 81,893 uniquely
owned declarations and separates 305,416 signature edges from 439,174
body/proof edges.

These were cache-preserving validation builds, not destructive clean-cache
benchmarks. Existing Lean linter and deprecation warnings remain visible; no
error was hidden or waived.

## Static architecture validation

| Gate | Result |
| --- | --- |
| Layout contract | passed: 772 modules |
| Exact legacy-debt ratchet | passed |
| Classified source boundary | passed: zero forbidden direct or reachable paths |
| Compatibility contract | passed: 43 wrappers, 44 canonical targets |
| Provenance contract | passed: 148 Apache files, 5 upstream modules |
| Aggregate ordering | passed: zero unsorted import-only aggregates |
| Apache normalization dry run | passed: zero files require changes |
| Architecture Python compilation | passed |
| `git diff --check` | passed |

The source-boundary result applies to the 120 reviewed modules. Classification
coverage is 15.544%, nine modules remain mixed, and the physical source-target
gate is therefore intentionally false.

## Captured artifacts

- [Human-readable architecture baseline](2026-07-22-organization-final.md)
- [Machine-readable architecture baseline](2026-07-22-organization-final.json)
- [Branch-wide migration record](../migrations/2026-07-22-organization.md)

The baseline identifies the uncommitted library paths included in the
candidate capture. A clean-checkout verification may be recorded against the
implementation commit containing this evidence rather than rewriting the dated
worktree capture.
