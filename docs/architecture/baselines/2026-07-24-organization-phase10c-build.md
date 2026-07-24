# Organization phase 10C build evidence (2026-07-24)

This record covers the numbering correction and semantic extraction for
Higham Chapter 2, Problems 2.22 and 2.23, developed on
`codex/organization-phase-10c-higham-chapter02` from the Phase 10B checkpoint
`db1711c5587f2b15d8a1344911f233b2f20b7233`. The immutable ownership map was
committed before implementation as
`6894545fa196371a11857089a3fb863ce7949ca6`.

Candidate-worktree and clean-commit validation are recorded separately. The
implementation revision is
`7f7d1e63d78293c1d64187d6419dd41bfc91cc27`. The architecture pair was then
recaptured from that clean revision and committed as
`233c798044ea9e40e2cd901795cb1b8f3afd84c8`. This evidence update changes no
Lean declaration, proof, import manifest, test, or captured measurement; its
only companion edit makes the transitional re-export removal policy explicit
in `COMPATIBILITY.md`.

## Environment

| Item | Value |
| --- | --- |
| Platform | Windows 11 |
| Lean toolchain | `leanprover/lean4:v4.29.0-rc3` |
| Mathlib revision | `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b` |
| Production target | `NumStability` |
| Test driver | `NumStabilityTest` |

## Migration result

The historical Chapter 2 numbering was one place behind the printed second
edition at this frontier. Phase 10C makes the printed numbering explicit:

- printed Problem 2.22 is now the canonical
  `Source.Higham.Chapter02.Problem22` locator for reusable
  `FloatingPoint.IEEE.NaiveMaximum`;
- printed Problem 2.23 now owns its two Heron theorems at
  `Source.Higham.Chapter02.Problem23`;
- historical `Analysis.Problem2_21` forwards to printed Problem 2.22; and
- historical `Analysis.Problem2_22` and `Higham.Chapter02.Problem22` forward
  directly to printed Problem 2.23.

The migration adds three production modules: the reusable naive-maximum leaf,
the declaration-free `FloatingPoint.IEEE` aggregate, and the canonical Problem
2.23 source leaf. The reusable `FloatingPoint` entry point and canonical
Chapter 2 aggregate expose the new paths. Seven isolated import tests cover the
new leaf and aggregate, both printed source locators, and all three historical
wrappers; the `FloatingPoint`, Chapter 2, Source, endpoint, compatibility,
all-library, and root smokes cover their entry-point surfaces.

All 18 compiled owned constants are preserved. The normalized comparisons are
exact:

| Family | Constants before/after | Signature edges | Body/proof edges |
| --- | ---: | ---: | ---: |
| IEEE naive maximum | 16 / 16 | 51 | 68 |
| Heron Problem 2.23 | 2 / 2 | 25 | 21 |

The first family contains 15 public declarations and one generated internal
constant; the second contains two public theorems. Names, kinds, visibility,
type structure, and body/proof structure match exactly after normalizing only
the two recorded owner moves. The global compiled graph is unchanged at
81,950 declarations and 491,557 union edges.

## Recorded departure from the immutable map

The pre-edit map specified that canonical
`Source.Higham.Chapter02.Problem22` would import only the reusable
`FloatingPoint.IEEE.NaiveMaximum` leaf. During implementation, the existing
canonical Problem 22 path was confirmed to be an already-supported public
import that exposed the Heron theorems. Removing that surface would have made
this organizational migration breaking.

The implemented locator therefore also imports
`Source.Higham.Chapter02.Problem23`. This transitional re-export preserves the
published surface while correcting ownership and printed numbering for new
code. The exception is documented in the module, `ARCHITECTURE.md`, and
`COMPATIBILITY.md`. It may be removed only in a planned breaking release after
an announced migration window; the historical one-import wrappers can remain
pointed at their correct canonical destinations.

## Candidate-worktree Lean validation

| Command or gate | Result |
| --- | --- |
| Fifteen focused canonical, aggregate, wrapper, and entry-point test modules | passed; 3,883 jobs |
| `lake test` | passed; 5,195 jobs |
| `lake build NumStability NumStabilityTest` | passed; 5,197 jobs |
| `lake env lean examples/LibraryLookup.lean` | passed |
| Compiled declaration-graph extraction | passed |
| Old-versus-new ownership and incident-edge audits | passed: exact 18-to-18 match |
| Strict-source baseline capture | passed |

These were cache-preserving validation builds. Existing Lean linter and
deprecation warnings remained visible; no error was hidden or waived.

## Architecture baseline

| Measure | Result |
| --- | ---: |
| Lean modules | 967 |
| Source lines | 1,468,116 |
| Direct imports | 4,023 |
| Internal import edges | 2,656 |
| External imports | 1,367 |
| Import cycles | 0 |
| Classified modules | 349 |
| Classification coverage | 36.091% |
| Mixed modules | 0 |
| Uniquely owned declarations | 81,950 |
| Public declarations | 56,187 |
| Private declarations | 4,341 |
| Internal declarations | 21,422 |
| Signature edges | 305,425 |
| Body/proof edges | 439,195 |
| Union edges | 491,557 |

The reviewed roles comprise 67 aggregates, 94 compatibility wrappers, two
internal modules, 51 reusable modules, 130 source modules, five upstream
modules, and zero reviewed mixed modules. There are zero direct or transitive
reusable-to-source or reusable-to-mixed paths.

Phase 10C reduces the unclassified inventory from 619 to 618, missing module
docstrings from 220 to 219, and historical naming exceptions from 412 to 411.
The compiled declaration and dependency graph remains exactly unchanged from
Phase 10B.

## Static validation

| Gate | Result |
| --- | --- |
| Layout, placeholder, test-reachability, and exact legacy-debt contract | passed: 967 modules |
| Classified source boundary | passed: zero forbidden direct or reachable paths |
| Compatibility contract | passed: 94 wrappers, 192 direct targets |
| Provenance contract | passed: 207 Apache files, five upstream modules |
| Aggregate structural and ordering contract | passed: 67 classified aggregates |
| Strict-source baseline | passed |
| Apache normalization dry run | passed: zero files require changes |
| Architecture Python syntax validation | passed: six files |
| Architecture JSON validation | passed: 17 files |
| Baseline reproducibility comparison | passed |
| `git diff --check` | passed |

The remaining exact debt is 618 unclassified modules, 219 missing module
docstrings, and 411 historical naming exceptions. There are zero reviewed mixed
modules, zero declaration-bearing umbrellas, and zero unsorted classified
aggregates. Partial classification means that the zero mixed count is a
ratchet, not a claim that every remaining historical module is already
semantically pure.

## Clean-commit verification

The worktree at implementation revision
`7f7d1e63d78293c1d64187d6419dd41bfc91cc27` was clean before validation. The
following results therefore validate committed source rather than an
uncommitted candidate:

| Command or gate | Result |
| --- | --- |
| Initial `git status --short` | passed: no output |
| `lake test` | passed; 5,195 jobs |
| `lake build NumStability NumStabilityTest` | passed; 5,197 jobs |
| `lake env lean examples/LibraryLookup.lean` | passed |
| Clean strict-source baseline capture | passed: 81,950 compiled declarations |
| Layout and exact legacy-debt contract | passed: 967 modules |
| Compatibility contract | passed: 94 wrappers, 192 direct targets |
| Provenance contract | passed: 207 Apache files, five upstream modules |

The clean capture changed only commit/cleanliness metadata in the generated
baseline pair. From clean baseline revision
`233c798044ea9e40e2cd901795cb1b8f3afd84c8`,
`generate_baseline.py --no-build --check --strict-source` passed against the
retained compiled dependency extraction. Notice normalization, Python syntax,
architecture JSON parsing, aggregate ordering, and `git diff --check` also
passed on the final source state.

## Captured artifacts

- [Human-readable architecture baseline](2026-07-24-organization-phase10c.md)
- [Machine-readable architecture baseline](2026-07-24-organization-phase10c.json)
- [Phase 10C migration and ownership record](../migrations/2026-07-24-higham-chapter02-problems22-23-phase10c.md)

The baseline records a clean production source tree at the implementation
revision. Its source, import, declaration, toolchain, and Mathlib measurements
were reproduced before this evidence-only commit.
