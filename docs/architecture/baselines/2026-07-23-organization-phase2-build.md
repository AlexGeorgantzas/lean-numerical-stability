# Organization phase 2 build evidence (2026-07-23)

This evidence covers the candidate worktree developed on
`codex/organization-phase-2` from
`aaffe408c169a4e6890f24953224e5423f1abc2e`. The checks ran before the
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
| `lake test` | passed; 4,757 of 4,757 jobs built |
| Focused summation and consumer rebuild | passed; 3,138 jobs built |
| `lake build NumStability NumStabilityTest` | passed; 4,759 jobs built |
| Full architecture-baseline build | passed; 4,647 jobs built |
| Compiled declaration extraction | passed |
| Baseline reproducibility check | passed |

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
| Layout contract | passed: 779 modules |
| Exact legacy-debt ratchet | passed |
| Classified source boundary | passed: zero forbidden direct or reachable paths |
| Compatibility contract | passed: 44 wrappers, 45 canonical targets |
| Provenance contract | passed: 148 Apache files, 5 upstream modules |
| Aggregate ordering | passed: zero unsorted import-only aggregates |
| `generate_baseline.py --strict-source` | passed |
| Apache normalization dry run | passed: zero files require changes |
| Architecture Python compilation | passed |
| `git diff --check` | passed |

The source-boundary result applies to the 127 reviewed modules. Classification
coverage is 16.303%; 652 modules remain unclassified and two modules remain
mixed. The broader physical source-target gate is therefore intentionally
false until classification is complete, while all currently classified
reusable modules have zero direct or transitive paths to source and mixed
modules.

The layout audit also records 227 missing module docstrings, 455 accepted
naming exceptions, one declaration-bearing umbrella, and zero unsorted
import-only aggregates. These exact inventories are ratchets for later phases,
not waived checks.

## Captured artifacts

- [Human-readable architecture baseline](2026-07-23-organization-phase2.md)
- [Machine-readable architecture baseline](2026-07-23-organization-phase2.json)
- [Phase 2 migration record](../migrations/2026-07-23-summation-phase2.md)

The baseline identifies the uncommitted library paths included in the
candidate capture. A clean-checkout verification may be recorded against the
implementation commit containing this evidence rather than rewriting the dated
worktree capture.
