# Organization phase 7 build evidence (2026-07-24)

This record covers the FastMatMul and Higham Chapter 23 migration developed on
`codex/organization-phase-7-fastmatmul` from
`4362b519c5bec29e0456fcb0a2cbee69924fa84e`.

Candidate-worktree validation and clean-checkout validation are recorded
separately. The declaration-bearing architecture capture was made from the
candidate worktree. A follow-up evidence-only commit will finalize the exact
implementation revision and clean-checkout rerun before this checkpoint is
pushed; until then, this record makes no clean-checkout claim.

## Environment

| Item | Value |
| --- | --- |
| Platform | Windows 11 |
| Lean toolchain | `leanprover/lean4:v4.29.0-rc3` |
| Mathlib revision | `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b` |
| Production target | `NumStability` |
| Test driver | `NumStabilityTest` |

## Migration result

The historical declaration-bearing `Algorithms.FastMatMul` root is now a
documented, sorted, declaration-free complete aggregate. Its reusable
recurrences moved to `Algorithms.FastMatMul.Recurrences`; its unsupported
legacy bound records moved to
`Algorithms.FastMatMul.Internal.LegacyBounds`.

The six historical `Algorithms.FastMatMul.Higham23*` implementation owners are
now exact import-only compatibility wrappers. Their 317 public declarations
and 20 source-written private declarations moved into 26 canonical declaration
leaves under `Source.Higham.Chapter23`. Five documented, sorted,
declaration-free aggregates provide the complete chapter, Theorem 23.2,
Theorem 23.3, Bini--Lotti, and 3M--Strassen import surfaces.

The migration adds 33 production modules: 26 canonical Chapter 23 leaves,
five Chapter 23 aggregates, one reusable recurrence leaf, and one internal
legacy-bounds leaf. All six old Chapter 23 paths preserve their exact
historical transitive surfaces without forwarding through a broader wrapper.
No production module imports an old Chapter 23 implementation path.

The root audit compared all 54 compiled constants elaborated from its nine
explicit declarations: 47 public and seven internal constants. Names, types,
bodies, visibility, and unique ownership were preserved. The Chapter 23 audit
compared normalized declaration bodies for all 317 public and 20
source-written private declarations against the immutable pre-migration
owners; all 20 private blocks are byte-identical after UTF-8/LF normalization.

Splitting seven declaration owners into 28 declaration-bearing leaves changes
file-boundary-dependent elaborator output. An exact Phase 6/Phase 7 TSV
comparison found 29 added and 12 removed matcher/proof helpers, for a net 17
additional non-public constants: seven private and ten internal, comprising
nine definitions and eight theorems. The migration record lists every helper
family. The public population remains exactly 56,187, and the normalized
public plus source-written-private declaration comparison has no difference.

Forty isolated tests cover every canonical leaf and aggregate, all six
old-only wrapper imports, the reusable recurrence surface, the internal legacy
compatibility surface, and the complete historical FastMatMul aggregate. Nine
shared entry-point smokes exercise the canonical hierarchy.

## Candidate-worktree Lean validation

| Command or gate | Result |
| --- | --- |
| All 26 canonical Chapter 23 declaration leaves | passed |
| All five canonical Chapter 23 aggregates | passed |
| Six old-only compatibility wrappers | passed |
| FastMatMul recurrence and complete-aggregate tests | passed |
| Wrapper, FastMatMul, and `Source.Higham` integration build | passed; 3,631 jobs |
| Nine shared entry-point import smokes | passed; 4,801 jobs |
| Registered `NumStabilityTest` target | passed before the final internal-surface smoke; final clean result recorded below |
| `lake test` | passed |
| `lake build NumStability NumStabilityTest` | passed before the final internal-surface smoke; final clean result recorded below |
| `lake env lean examples/LibraryLookup.lean` | passed |
| Full architecture-baseline production build | passed; 4,773 jobs |
| Compiled declaration extraction | passed |
| Baseline reproducibility comparison | passed |

These were cache-preserving validation builds. Existing Lean linter and
deprecation warnings remained visible; no error was hidden or waived.

## Architecture baseline

| Measure | Result |
| --- | ---: |
| Lean modules | 931 |
| Source lines | 1,467,718 |
| Direct imports | 3,972 |
| Import cycles | 0 |
| Classified modules | 294 |
| Classification coverage | 31.579% |
| Mixed modules | 0 |
| Uniquely owned declarations | 81,950 |
| Public declarations | 56,187 |
| Private declarations | 4,341 |
| Internal declarations | 21,422 |
| Signature edges | 305,425 |
| Body/proof edges | 439,195 |

Phase 7 increases the classified inventory from 254 to 294 modules. The
reviewed roles comprise 56 aggregates, 70 compatibility wrappers, two internal
modules, 49 reusable modules, 112 source modules, five upstream modules, and
zero mixed modules. There are zero direct or transitive reusable-to-source or
reusable-to-mixed paths.

All 33 new production modules are classified at creation. The seven previously
unclassified historical owners are now classified, reducing the unclassified
inventory from 644 to 637 despite the larger source tree.

## Static validation

| Gate | Result |
| --- | --- |
| Layout and exact legacy-debt contract | passed: 931 modules |
| Placeholder and test-reachability gate | passed |
| Classified source boundary | passed: zero forbidden direct or reachable paths |
| Compatibility contract | passed: 70 wrappers, 168 direct targets |
| Provenance contract | passed: 205 Apache files, five upstream modules |
| Aggregate structural contract | passed: every aggregate declaration-free |
| Aggregate ordering | passed for all 56 classified aggregates |
| Strict-source baseline | passed |
| Apache normalization dry run | passed: zero files require changes |
| Architecture Python syntax validation | passed |
| Architecture JSON validation | passed: 12 files |
| Baseline reproducibility comparison | passed |
| `git diff --check` | passed |

The remaining exact debt is 637 unclassified modules, 224 missing module
docstrings, and 431 historical naming exceptions. There are zero mixed
modules, zero declaration-bearing umbrellas, and zero unsorted aggregates.

## Clean-checkout verification

The implementation revision and its clean-checkout command results are
intentionally deferred to the evidence-only follow-up described above. That
follow-up will record a clean status before validation, `lake test`, the full
production/test build, the library lookup example, baseline reproducibility,
and the final static-gate rerun.

## Captured artifacts

- [Human-readable architecture baseline](2026-07-24-organization-phase7.md)
- [Machine-readable architecture baseline](2026-07-24-organization-phase7.json)
- [Phase 7 migration record](../migrations/2026-07-24-fastmatmul-chapter23-phase7.md)

The baseline records the exact dirty production paths included in the
candidate capture. Its stable source, import, declaration, toolchain, and
Mathlib measurements will be reproduced from the clean implementation
checkout before push.
