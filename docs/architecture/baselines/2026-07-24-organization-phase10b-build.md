# Organization phase 10B build evidence (2026-07-24)

This record covers the compatibility-preserving small-frontier migration for
Higham Chapters 2, 14, 21, and 28 developed on
`codex/organization-phase-10b-small-frontiers` from
`21e130ac8355de8ec1a74f22a73bf103e00bc48f`. The immutable ownership map was
committed before implementation as
`35f16880999fbfad0707dd4850df0fb9d9b5d7f9`.

Candidate-worktree and clean-commit validation are recorded separately. The
implementation revision is
`91dd4db602515f12e9aa054396ac4ea27f84d1bb`. After the final aggregate-import
ordering fix, the architecture pair was recaptured from that clean revision
and committed as `11bee936dae28eb6e0f39a2f6ae1a4386eed6eb9`. This
evidence-only update changes no Lean source, architecture manifest, test, or
captured measurement.

## Environment

| Item | Value |
| --- | --- |
| Platform | Windows 11 |
| Lean toolchain | `leanprover/lean4:v4.29.0-rc3` |
| Mathlib revision | `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b` |
| Production target | `NumStability` |
| Test driver | `NumStabilityTest` |

## Migration result

Four historical declaration owners moved one-for-one to semantic owners:

- `Analysis.Problem2_2` to `Source.Higham.Chapter02.Problem02`;
- `Algorithms.Ch14Problem1413Boundary` to
  `Source.Higham.Chapter14.Problem13`;
- `Algorithms.Underdetermined.Higham21Condition` to
  `Source.Higham.Chapter21.RowScalingInvariance`; and
- `Algorithms.TestMatrices.Higham28GaussianAbsoluteMoment` to the reusable
  `Analysis.Probability.Gaussian.AbsoluteMoment` API.

The migration adds seven canonical production modules: four declaration
leaves and three documented, sorted, declaration-free aggregates. Every old
path is an exact one-import compatibility wrapper, and no production module
imports any of the four historical implementation paths. Eleven registered
isolated tests cover all canonical leaves, all new aggregates, and every
old-only wrapper import; the shared source, analysis, algorithms, endpoint,
all-library, and root smokes cover the changed entry-point surfaces.

All 43 compiled owned constants are preserved: 22 public constants and 21
generated internal constants. The normalized per-family comparisons are
exact:

| Family | Constants before/after | Signature edges | Body/proof edges |
| --- | ---: | ---: | ---: |
| Chapter 2 Problem 2.2 | 3 / 3 | 12 | 15 |
| Chapter 14 Problem 14.13 | 5 / 5 | 13 | 32 |
| Chapter 21 row scaling | 27 / 27 | 16 | 23 |
| Gaussian absolute moment | 8 / 8 | 0 | 8 |

Names, owners after normalizing only the four recorded module moves, kinds,
visibility, type structure, and body/proof structure match exactly. The global
compiled graph is unchanged at 81,950 declarations and 491,557 union edges.

## Candidate-worktree Lean validation

| Command or gate | Result |
| --- | --- |
| Four canonical leaves, three new aggregates, and four old-only wrapper tests | passed |
| All eleven isolated tests | passed |
| `lake test` | passed; 5,187 jobs |
| `lake build NumStability NumStabilityTest` | passed; 5,189 jobs |
| `lake env lean examples/LibraryLookup.lean` | passed |
| Compiled declaration-graph extraction | passed |
| Four old-versus-new ownership and incident-edge audits | passed: exact 43-to-43 match |
| Strict baseline comparison | passed |

These were cache-preserving validation builds. Existing Lean linter and
deprecation warnings remained visible; no error was hidden or waived.

## Architecture baseline

| Measure | Result |
| --- | ---: |
| Lean modules | 964 |
| Source lines | 1,468,075 |
| Direct imports | 4,018 |
| Internal import edges | 2,651 |
| External imports | 1,367 |
| Import cycles | 0 |
| Classified modules | 345 |
| Classification coverage | 35.788% |
| Mixed modules | 0 |
| Uniquely owned declarations | 81,950 |
| Public declarations | 56,187 |
| Private declarations | 4,341 |
| Internal declarations | 21,422 |
| Signature edges | 305,425 |
| Body/proof edges | 439,195 |
| Union edges | 491,557 |

The reviewed roles comprise 66 aggregates, 93 compatibility wrappers, two
internal modules, 50 reusable modules, 129 source modules, five upstream
modules, and zero reviewed mixed modules. There are zero direct or transitive
reusable-to-source or reusable-to-mixed paths.

Phase 10B classifies all seven new production modules and all four historical
wrappers, reducing the unclassified inventory from 623 to 619. The global
declaration and dependency graph remains exactly unchanged from Phase 10A.

## Static validation

| Gate | Result |
| --- | --- |
| Layout, placeholder, test-reachability, and exact legacy-debt contract | passed: 964 modules |
| Classified source boundary | passed: zero forbidden direct or reachable paths |
| Compatibility contract | passed: 93 wrappers, 191 direct targets |
| Provenance contract | passed: 207 Apache files, five upstream modules |
| Aggregate structural and ordering contract | passed: 66 classified aggregates |
| Strict-source baseline | passed |
| Apache normalization dry run | passed: zero files require changes |
| Architecture Python syntax validation | passed: six files |
| Architecture JSON validation | passed: 16 files |
| Baseline reproducibility comparison | passed |
| `git diff --check` | passed |

The remaining exact debt is 619 unclassified modules, 220 missing module
docstrings, and 412 historical naming exceptions. There are zero reviewed
mixed modules, zero declaration-bearing umbrellas, and zero unsorted
classified aggregates. Partial classification means that the zero mixed count
is a ratchet, not a claim that every remaining historical module is already
semantically pure.

## Clean-commit verification

The worktree at implementation revision
`91dd4db602515f12e9aa054396ac4ea27f84d1bb` was clean before validation. The
following results therefore validate committed source rather than an
uncommitted candidate:

| Command or gate | Result |
| --- | --- |
| Initial `git status --short` | passed: no output |
| `lake test` | passed; 5,187 jobs |
| `lake build NumStability NumStabilityTest` | passed; 5,189 jobs |
| `lake env lean examples/LibraryLookup.lean` | passed |
| Clean strict-source baseline capture | passed: 81,950 compiled declarations |
| Layout and exact legacy-debt contract | passed: 964 modules |
| Compatibility contract | passed: 93 wrappers, 191 direct targets |
| Provenance contract | passed: 207 Apache files, five upstream modules |

The clean capture corrected only capture metadata and the production
source-tree digest after the final import-order normalization; all substantive
source, import, tier, and declaration measurements remained identical. From
clean baseline revision `11bee936dae28eb6e0f39a2f6ae1a4386eed6eb9`,
`generate_baseline.py --no-build --check --strict-source` passed against the
retained compiled dependency extraction. Notice normalization, Python syntax,
architecture JSON parsing, aggregate ordering, and `git diff --check` also
passed on the final source state.

## Captured artifacts

- [Human-readable architecture baseline](2026-07-24-organization-phase10b.md)
- [Machine-readable architecture baseline](2026-07-24-organization-phase10b.json)
- [Phase 10B migration and ownership record](../migrations/2026-07-24-small-higham-frontiers-phase10b.md)

The baseline records a clean production source tree at the implementation
revision. Its source, import, declaration, toolchain, and Mathlib measurements
were reproduced before this evidence-only commit.
