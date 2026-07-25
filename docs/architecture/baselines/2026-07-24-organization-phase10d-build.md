# Organization phase 10D build evidence (2026-07-24)

This record covers the semantic reorganization of the Higham Chapter 2
leading-digit family. Development started from the Phase 10C checkpoint
`ce3811681e9a9a1c6d4a334b9928e12210232832` on
`codex/organization-phase-10d-higham-chapter02-leading-digits`. The immutable
ownership map was committed before implementation as
`2d12e65278a62565d01f12277f6b8a23003424e2`.

Candidate-worktree and clean-commit validation are recorded separately. The
implementation revision is
`de41cba2e35e1b729c17a10f34a25e19b957da0f`. The architecture pair was then
recaptured from that clean revision and committed as
`385d513d84aa7bef097797656b9e2568bb3811b0`. This evidence update changes no
Lean declaration, proof, import, manifest, test, or captured measurement.

## Environment

| Item | Value |
| --- | --- |
| Platform | Windows 11 |
| Lean toolchain | `leanprover/lean4:v4.29.0-rc3` |
| Mathlib revision | `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b` |
| Production target | `NumStability` |
| Test driver | `NumStabilityTest` |

## Migration result

The three historical flat owners mixed reusable analysis, printed-source
material, and a final source conclusion. Phase 10D assigns them to semantic
owners:

- reusable AddCircle orbit, Fourier/Haar, and frequency results live at
  `Analysis.Equidistribution.AddCircle`;
- reusable decimal predicates, empirical histograms, the logarithmic law, and
  decimal-power reductions live below `Analysis.LeadingDigits`;
- Problem 2.11's enumerated survey sources and exact power/factorial samples
  live at `Source.Higham.Chapter02.Problem11`; and
- the precise Section 2.7 power-frequency conclusion lives at
  `Source.Higham.Chapter02.Section07.PowerLeadingDigits`.

`Analysis.Equidistribution`, `Analysis.LeadingDigits`, and
`Source.Higham.Chapter02.Section07` are declaration-free family aggregates.
The historical `Analysis.LeadingDigitDistribution`, `Analysis.Problem2_11`,
and `Analysis.HighamChapter2PowerLeadingDigits` paths are import-only
compatibility wrappers. The last wrapper forwards to both canonical Problem 11
and Section 2.7 leaves because the old module transitively exposed the complete
Problem 2.11 surface as well as its own power theorem.

The migration adds ten production modules and thirteen isolated one-import
tests. Canonical Analysis, Chapter 2, Source, endpoint, migration, public API,
All, and root smokes exercise the new and historical entry-point surfaces.

## Exact compiled ownership and dependency preservation

The Phase 10C dependency stream was SHA-256 guarded at
`2D0248865CB2F8450ADE1C98A87753190CEDED804C00305FDD06D354E777BCB0` before
comparison. After normalizing only the mapped module owner for each name, the
complete declaration metadata and both dependency-edge sets match exactly.

| Canonical owner | Total | Public | Private | Internal | Signature edges | Body/proof edges |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Analysis.LeadingDigits.LogarithmicDistribution` | 26 | 23 | 0 | 3 | 43 | 59 |
| `Analysis.LeadingDigits.Decimal` | 6 | 5 | 0 | 1 | 3 | 7 |
| `Analysis.LeadingDigits.Empirical` | 14 | 12 | 0 | 2 | 17 | 25 |
| `Source.Higham.Chapter02.Problem11` | 57 | 50 | 0 | 7 | 111 | 135 |
| `Analysis.Equidistribution.AddCircle` | 41 | 34 | 0 | 7 | 39 | 90 |
| `Analysis.LeadingDigits.DecimalPowers` | 27 | 18 | 0 | 9 | 22 | 43 |
| `Source.Higham.Chapter02.Section07.PowerLeadingDigits` | 1 | 1 | 0 | 0 | 3 | 13 |

The family total is 172 compiled constants: 143 public, zero private, and 29
generated internal constants. The comparator checked the exact declaration
name set, kind and visibility per name, expected owner per name, and every
signature and body/proof edge. The global graph is unchanged at 81,950
declarations, 305,425 signature edges, 439,195 body/proof edges, and 491,557
union edges.

## Recorded departure from the immutable map

There is no departure from the mapped production tree, declaration ownership,
wrapper surface, aggregate surface, or test plan. Two forecast debt totals in
the immutable record were one lower than the scanner-supported result:

- the map forecast 218 missing module docs, but the result is 219; and
- the map forecast 408 legacy naming exceptions, but the result is 409.

The cause is structural, not an implementation omission. All three historical
owners already contained module docstrings, so classifying them as wrappers
does not reduce the missing-doc queue. Only
`Analysis.HighamChapter2PowerLeadingDigits` and `Analysis.Problem2_11` were
legacy naming exceptions; `Analysis.LeadingDigitDistribution` was already a
canonical UpperCamel module name. No unrelated debt was changed merely to
force the forecast. The evidence-backed 219/409 values are used consistently
in the ratchet manifests and documentation.

## Candidate-worktree Lean validation

| Command or gate | Result |
| --- | --- |
| Seven focused production leaves | passed; 2,773 jobs |
| Thirteen isolated aggregate, leaf, source, and wrapper tests | passed; 2,792 jobs |
| `lake build NumStability` | passed; 4,780 jobs |
| `lake test` | passed; 5,206 jobs |
| `lake build NumStability NumStabilityTest` | passed; 5,208 jobs |
| `lake env lean examples/LibraryLookup.lean` | passed |
| Compiled declaration-graph extraction | passed |
| Exact old-versus-new name, metadata, ownership, and edge comparison | passed: exact 172-to-172 match |
| Strict-source baseline capture and reproducibility check | passed |

These were cache-preserving validation builds. Existing Lean linter and
deprecation warnings remained visible; no error was hidden or waived.

## Architecture baseline

| Measure | Result |
| --- | ---: |
| Lean modules | 977 |
| Source lines | 1,468,282 |
| Nonblank source lines | 1,402,087 |
| Direct imports | 4,041 |
| Internal import edges | 2,673 |
| External imports | 1,368 |
| Import cycles | 0 |
| Classified modules | 362 |
| Classification coverage | 37.052% |
| Mixed modules | 0 |
| Uniquely owned declarations | 81,950 |
| Public declarations | 56,187 |
| Private declarations | 4,341 |
| Internal declarations | 21,422 |
| Signature edges | 305,425 |
| Body/proof edges | 439,195 |
| Union edges | 491,557 |

The reviewed roles comprise 70 aggregates, 97 compatibility wrappers, two
internal modules, 56 reusable modules, 132 source modules, five upstream
modules, and zero reviewed mixed modules. There are zero direct or transitive
reusable-to-source or reusable-to-mixed paths.

Phase 10D reduces the unclassified inventory from 618 to 615 and historical
naming exceptions from 411 to 409. The missing-module-doc inventory remains
219. The compiled declaration and dependency graph remains exactly unchanged
from Phase 10C.

## Static validation

| Gate | Result |
| --- | --- |
| Layout, placeholder, test-reachability, and exact legacy-debt contract | passed: 977 modules |
| Classified source boundary | passed: zero forbidden direct or reachable paths |
| Compatibility contract | passed: 97 wrappers, 196 direct targets |
| Provenance contract | passed: 207 Apache files, five upstream modules |
| Aggregate structural and ordering contract | passed: 70 classified aggregates |
| Strict-source baseline | passed |
| Baseline reproducibility comparison | passed |
| Independent complete-diff audit | passed: no findings |
| `git diff --check` | passed |

The remaining exact debt is 615 unclassified modules, 219 missing module
docstrings, and 409 historical naming exceptions. There are zero reviewed mixed
modules, zero declaration-bearing umbrellas, and zero unsorted classified
aggregates. Partial classification means that the zero mixed count is a
ratchet, not a claim that every remaining historical module is already
semantically pure.

## Clean-commit verification

The production tree at implementation revision
`de41cba2e35e1b729c17a10f34a25e19b957da0f` was clean when the architecture
pair was recaptured. The following gates were then repeated from committed
source; the baseline-only commit changes no production or test input:

| Command or gate | Result |
| --- | --- |
| Initial `git status --short` | passed: no output |
| `lake test` | passed; 5,206 jobs |
| `lake build NumStability NumStabilityTest` | passed; 5,208 jobs |
| `lake env lean examples/LibraryLookup.lean` | passed |
| Clean strict-source baseline capture | passed: 81,950 compiled declarations |
| Layout and exact legacy-debt contract | passed: 977 modules |
| Compatibility contract | passed: 97 wrappers, 196 direct targets |
| Provenance contract | passed: 207 Apache files, five upstream modules |
| Baseline `--check` against the retained dependency extraction | passed |

The clean capture changed only commit and cleanliness metadata in the generated
baseline pair. The baseline records `library_source_clean: true` at the
implementation revision.

## Captured artifacts

- [Human-readable architecture baseline](2026-07-24-organization-phase10d.md)
- [Machine-readable architecture baseline](2026-07-24-organization-phase10d.json)
- [Phase 10D migration and ownership record](../migrations/2026-07-24-higham-chapter02-leading-digits-phase10d.md)

The source, import, declaration, toolchain, and Mathlib measurements were
reproduced before this evidence-only commit.
