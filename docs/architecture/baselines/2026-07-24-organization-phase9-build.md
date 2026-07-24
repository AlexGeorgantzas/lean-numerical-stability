# Organization phase 9 build evidence (2026-07-24)

This record covers the compatibility-preserving Higham Chapters 12, 13, 22,
and 27 migration developed on
`codex/organization-phase-9-small-source-families` from
`943289eaa350f4430292e177f5d7ef876afb08af`. The immutable ownership map was
committed before implementation as
`15b33b323e0ab101620d17c82e99fb754c4a36a6`.

Candidate-worktree validation and clean-commit validation are recorded
separately. The declaration-bearing architecture capture was made from the
candidate worktree and reproduced from the clean implementation revision
`eb64d33bb25e271bd0d7e4140e7b7f7a675562b3`. This evidence-only update changes
no Lean source, architecture manifest, test, or captured baseline.

## Environment

| Item | Value |
| --- | --- |
| Platform | Windows 11 |
| Lean toolchain | `leanprover/lean4:v4.29.0-rc3` |
| Mathlib revision | `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b` |
| Production target | `NumStability` |
| Test driver | `NumStabilityTest` |

## Migration result

Eleven historical declaration owners moved one-for-one into semantic leaves
under `Source.Higham.Chapter12`, `Chapter13`, `Chapter22`, and `Chapter27`.
The new Chapter 12, Chapter 22, Chapter 22 Section 3, and Chapter 27 modules
are documented, sorted, declaration-free aggregates; the existing Chapter 13
aggregate now includes the Demmel sharp-multiplier leaf. All eleven old paths
are exact one-import compatibility wrappers, and no production module imports
one of those historical implementation paths.

The migration adds fifteen canonical production modules: eleven declaration
owners and four aggregates. Twenty-six isolated tests cover every canonical
leaf and aggregate and every old-only wrapper import. Eight shared entry-point
smokes exercise `Algorithms`, `All`, `Higham`, the root, `Source`,
`Source.Higham`, `SourceCanonical`, and `SourceMigration`.

All 835 source-written declaration blocks, including 13 private blocks, are
preserved. An isolated old-versus-new compiled audit compared all 2,217 owned
constants: 1,043 public, 1,093 internal, and 81 private. After normalizing only
the eleven recorded owner paths and their occurrences in private names and
hygienic universe-level parameter names, there are zero missing, added, owner,
kind, visibility, type, or proof/body mismatches. The comparison erased no
metadata, constants, universe levels, applications, types, or proof structure.

The per-family compiled populations are 62 constants for Chapter 12, 53 for
Chapter 13, 1,730 for Chapter 22, and 372 for Chapter 27. Their combined kinds
are 15 constructors, 497 definitions, 10 inductives, 10 recursors, and 1,685
theorems.

## Candidate-worktree Lean validation

| Command or gate | Result |
| --- | --- |
| Eleven canonical declaration leaves and four aggregates | passed |
| Twenty-six isolated tests plus eight shared entry-point smokes | passed |
| Registered `NumStabilityTest` target | passed; 5,159 jobs |
| `lake test` | passed; 5,158 jobs |
| `lake build NumStability NumStabilityTest` | passed; 5,160 jobs |
| `lake env lean examples/LibraryLookup.lean` | passed |
| Full architecture-baseline production build | passed; 4,779 jobs |
| Compiled old-versus-new declaration audit | passed: exact 2,217-to-2,217 match |
| Baseline reproducibility comparison | passed |

These were cache-preserving validation builds. Existing Lean linter and
deprecation warnings remained visible; no error was hidden or waived.

## Architecture baseline

| Measure | Result |
| --- | ---: |
| Lean modules | 953 |
| Source lines | 1,467,961 |
| Direct imports | 4,004 |
| Internal import edges | 2,637 |
| Import cycles | 0 |
| Classified modules | 327 |
| Classification coverage | 34.313% |
| Mixed modules | 0 |
| Uniquely owned declarations | 81,950 |
| Public declarations | 56,187 |
| Private declarations | 4,341 |
| Internal declarations | 21,422 |
| Signature edges | 305,425 |
| Body/proof edges | 439,195 |
| Union edges | 491,557 |

The reviewed roles comprise 62 aggregates, 86 compatibility wrappers, two
internal modules, 49 reusable modules, 123 source modules, five upstream
modules, and zero mixed modules. There are zero direct or transitive
reusable-to-source or reusable-to-mixed paths.

The declaration graph is exactly unchanged from Phase 8: every declaration,
visibility, and global signature, body/proof, and union edge count is
identical. Phase 9 classifies all fifteen new production modules and all eleven
historical wrappers, reducing the unclassified inventory from 637 to 626.

## Static validation

| Gate | Result |
| --- | --- |
| Layout and exact legacy-debt contract | passed: 953 modules |
| Placeholder and test-reachability gate | passed |
| Classified source boundary | passed: zero forbidden direct or reachable paths |
| Compatibility contract | passed: 86 wrappers, 184 direct targets |
| Provenance contract | passed: 207 Apache files, five upstream modules |
| Aggregate structural contract | passed: every aggregate declaration-free |
| Aggregate ordering | passed for all 62 classified aggregates |
| Strict-source baseline | passed |
| Apache normalization dry run | passed: zero files require changes |
| Architecture Python syntax validation | passed |
| Architecture JSON validation | passed: 14 files |
| Baseline reproducibility comparison | passed |
| `git diff --check` | passed |

The remaining exact debt is 626 unclassified modules, 222 missing module
docstrings, and 419 historical naming exceptions. There are zero mixed
modules, zero declaration-bearing umbrellas, and zero unsorted aggregates.

## Clean-commit verification

The worktree at revision `eb64d33bb25e271bd0d7e4140e7b7f7a675562b3`
was clean before validation. The following results therefore validate the
committed implementation rather than an uncommitted candidate:

| Command or gate | Result |
| --- | --- |
| Initial `git status --short` | passed: no output |
| `lake test` | passed; 5,158 jobs |
| `lake build NumStability NumStabilityTest` | passed; 5,160 jobs |
| `lake env lean examples/LibraryLookup.lean` | passed |
| `generate_baseline.py --no-build --check` | passed: exact reproduction |
| Layout and exact legacy-debt contract | passed: 953 modules |
| Compatibility contract | passed: 86 wrappers, 184 direct targets |
| Provenance contract | passed: 207 Apache files, five upstream modules |
| Strict-source baseline | passed |
| Aggregate ordering | passed for all 62 classified aggregates |
| Apache normalization dry run | passed: zero files require changes |
| Architecture Python syntax validation | passed |
| Architecture JSON validation | passed: 14 files |

## Captured artifacts

- [Human-readable architecture baseline](2026-07-24-organization-phase9.md)
- [Machine-readable architecture baseline](2026-07-24-organization-phase9.json)
- [Phase 9 migration and ownership record](../migrations/2026-07-24-higham-chapters12-13-22-27-phase9.md)

The baseline records the exact production paths included in the candidate
capture. Its source, import, declaration, toolchain, and Mathlib measurements
were reproduced exactly from the clean implementation commit before push.
