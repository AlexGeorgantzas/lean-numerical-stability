# Organization phase 8 build evidence (2026-07-24)

This record covers the Higham Chapter 1 Section 1.17 nonrandom-rounding
migration developed on `codex/organization-phase-8-higham-chapter01` from
`e27c25af3d975dfc9e9032e94b6dd06cfe057a42`. The immutable ownership map was
committed before implementation as
`64158516786c59ced1cf892741669fe908876752`.

Candidate-worktree validation and clean-checkout validation are recorded
separately. The implementation revision is filled in by the evidence-only
follow-up after the committed candidate is validated from a clean worktree.

## Environment

| Item | Value |
| --- | --- |
| Platform | Windows 11 |
| Lean toolchain | `leanprover/lean4:v4.29.0-rc3` |
| Mathlib revision | `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b` |
| Production target | `NumStability` |
| Test driver | `NumStabilityTest` |

## Migration result

Five historical declaration owners under `Analysis.NonrandomRounding` moved
one-for-one into semantic leaves under
`Source.Higham.Chapter01.Section17`. The new Section 1.17 and Chapter 1
modules are documented, sorted, declaration-free aggregates. The six old
paths are exact one-import compatibility wrappers, and no production module
imports one of those historical paths.

The canonical dependency chain remains Horner evaluation, source interval,
grid variation, stored grid, and final error-spread conclusions. The broad
`Analysis` entry point imports the canonical Section 1.17 aggregate directly
to preserve its existing transitive public surface. `Source.Higham` now
imports the canonical Chapter 1 aggregate.

An isolated old-versus-new compiled audit compared all 242 owned constants:
164 public, 65 internal, and 13 private. After normalizing only the five owner
paths and the two expected `_private` module prefixes, there are zero missing,
added, or mismatched names, owners, kinds, visibility markers, types, or
bodies/proofs under Lean's structural hashes. The per-owner distributions are
exactly 108, 21, 63, 41, and 9 constants, so the move produces no helper
delta. All 147 source-written
declaration blocks, including 13 private blocks, are byte-identical; only
headers, imports, module documentation, and one pre-recorded orphan trailing
comment differ.

Thirteen isolated tests cover the five canonical leaves, both canonical
aggregates, and all six old-only wrapper imports. Eight shared entry-point
smokes exercise the changed canonical and compatibility surfaces.

## Candidate-worktree Lean validation

| Command or gate | Result |
| --- | --- |
| Five canonical declaration leaves and two aggregates | passed; 3,630 jobs |
| Thirteen isolated tests plus shared entry-point smokes | passed; 4,821 jobs |
| Registered `NumStabilityTest` target | passed; 5,118 jobs |
| `lake test` | passed; 5,117 jobs |
| `lake build NumStability NumStabilityTest` | passed; 5,119 jobs |
| `lake env lean examples/LibraryLookup.lean` | passed |
| Full architecture-baseline production build | passed; 4,775 jobs |
| Compiled old-versus-new declaration audit | passed: exact 242-to-242 match |
| Baseline reproducibility comparison | passed |

These were cache-preserving validation builds. Existing Lean linter and
deprecation warnings remained visible; no error was hidden or waived.

## Architecture baseline

| Measure | Result |
| --- | ---: |
| Lean modules | 938 |
| Source lines | 1,467,799 |
| Direct imports | 3,984 |
| Import cycles | 0 |
| Classified modules | 301 |
| Classification coverage | 32.090% |
| Mixed modules | 0 |
| Uniquely owned declarations | 81,950 |
| Public declarations | 56,187 |
| Private declarations | 4,341 |
| Internal declarations | 21,422 |
| Signature edges | 305,425 |
| Body/proof edges | 439,195 |

The reviewed roles comprise 58 aggregates, 75 compatibility wrappers, two
internal modules, 49 reusable modules, 112 source modules, five upstream
modules, and zero mixed modules. There are zero direct or transitive
reusable-to-source or reusable-to-mixed paths.

Phase 8 classifies all seven new production modules at creation and classifies
all six historical wrappers. The unclassified inventory therefore remains
637 while the production tree grows by seven modules. The declaration graph
is exactly unchanged from Phase 7: every declaration and global edge count is
identical.

## Static validation

| Gate | Result |
| --- | --- |
| Layout and exact legacy-debt contract | passed: 938 modules |
| Placeholder and test-reachability gate | passed |
| Classified source boundary | passed: zero forbidden direct or reachable paths |
| Compatibility contract | passed: 75 wrappers, 173 direct targets |
| Provenance contract | passed: 205 Apache files, five upstream modules |
| Aggregate structural contract | passed: every aggregate declaration-free |
| Aggregate ordering | passed for all 58 classified aggregates |
| Strict-source baseline | passed |
| Apache normalization dry run | passed: zero files require changes |
| Architecture Python syntax validation | passed |
| Architecture JSON validation | passed: 13 files |
| Baseline reproducibility comparison | passed |
| `git diff --check` | passed |

The remaining exact debt is 637 unclassified modules, 224 missing module
docstrings, and 430 historical naming exceptions. There are zero mixed
modules, zero declaration-bearing umbrellas, and zero unsorted aggregates.

## Clean-checkout verification

The implementation revision and its clean-checkout results are recorded in
an evidence-only follow-up commit after the candidate implementation is
committed. No Lean source, architecture manifest, test, or generated baseline
will change in that follow-up.

## Captured artifacts

- [Human-readable architecture baseline](2026-07-24-organization-phase8.md)
- [Machine-readable architecture baseline](2026-07-24-organization-phase8.json)
- [Phase 8 migration record](../migrations/2026-07-24-higham-chapter01-nonrandom-rounding-phase8.md)

The baseline records the exact production paths included in the candidate
capture. Its source, import, declaration, toolchain, and Mathlib measurements
must reproduce exactly from the clean implementation checkout before push.
