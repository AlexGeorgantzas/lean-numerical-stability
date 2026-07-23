# Organization phase 3 build evidence (2026-07-23)

This evidence covers the candidate worktree developed on
`codex/organization-phase-3` from
`3b3955a822d9f4cfbf19a957f9eadb21ab1b22f5`. The checks ran before the
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
| Isolated insertion-leaf builds | passed |
| Focused insertion, source, consumer, family, and compatibility rebuild | passed; 3,174 jobs built |
| `lake test` | passed; 4,770 of 4,770 jobs built |
| `lake build NumStability NumStabilityTest` | passed; 4,772 jobs built |
| Full architecture-baseline build | passed; 4,653 jobs built |
| Compiled declaration extraction | passed |
| Baseline reproducibility check | passed |

The isolated checks compile all five reusable insertion layers, the Chapter 4
source leaf, the complete family surface, and the old-only compatibility
surface independently. The full baseline records 81,896 uniquely owned
declarations, retains the Phase 2 public-declaration count of 56,186, and
separates 305,417 signature edges from 439,175 body/proof edges.

These were cache-preserving validation builds, not destructive clean-cache
benchmarks. Existing Lean linter and deprecation warnings remain visible; no
error was hidden or waived.

## Static architecture validation

| Gate | Result |
| --- | --- |
| Layout contract | passed: 785 modules |
| Exact legacy-debt ratchet | passed |
| Classified source boundary | passed: zero forbidden direct or reachable paths |
| Compatibility contract | passed: 44 wrappers, 45 canonical targets |
| Provenance contract | passed: 148 Apache files, 5 upstream modules |
| Aggregate ordering | passed: zero unsorted import-only aggregates |
| `generate_baseline.py --strict-source` | passed |
| Apache normalization dry run | passed: zero files require changes |
| Architecture Python compilation | passed |
| `git diff --check` | passed |

The source-boundary result applies to the 133 reviewed modules. Classification
coverage is 16.943%; 652 modules remain unclassified and one module remains
mixed. The broader physical source-target gate is therefore intentionally
false until classification is complete, while all currently classified
reusable modules have zero direct or transitive paths to source and mixed
modules.

The layout audit also records 227 missing module docstrings, 455 accepted
naming exceptions, one declaration-bearing umbrella, and zero unsorted
import-only aggregates. These exact inventories are ratchets for later phases,
not waived checks.

## Captured artifacts

- [Human-readable architecture baseline](2026-07-23-organization-phase3.md)
- [Machine-readable architecture baseline](2026-07-23-organization-phase3.json)
- [Phase 3 migration record](../migrations/2026-07-23-insertion-phase3.md)

The baseline identifies the uncommitted library paths included in the
candidate capture. A clean-checkout verification may be recorded against the
implementation commit containing this evidence rather than rewriting the dated
worktree capture.
