# Organization Phase 11A build evidence (2026-07-26)

This record covers the bounded source-tail extraction from the historical
`Analysis.Norms` monolith. The 1,783-constant residual implementation now
lives at `Analysis.Norms.Core`; the 21-constant ambient-radius realization of
Higham's Theorem 6.4 lives at
`Source.Higham.Chapter06.Theorem04`. The historical path is an import-only
two-target compatibility facade.

Development started from the pushed Phase 10F checkpoint
`41fd9fa61336d33f0a197f6620975f5b9b3de714` on
`codex/organization-phase-11-analysis-norms`. The immutable ownership map was
committed before implementation as
`20a9bbc7149372827f75c1c34be28d2029f620f0`.

Candidate-worktree and clean-commit validation are recorded separately. The
implementation revision is
`63719a150fceecaa132f7c2ba5b57ba07e28bec7`. The architecture pair was
captured from that clean revision and committed as
`4a876070ed138e9dc08e4f975c8830c87702b7d5`. This evidence update changes no
Lean declaration, proof, import, manifest, test, or captured measurement.

## Environment

| Item | Value |
| --- | --- |
| Platform | Windows 11 |
| Lean toolchain | leanprover/lean4:v4.29.0-rc3 |
| Mathlib revision | e8ea1afc32790ce1d4e1a4e45cc412ba9388716b |
| Production target | NumStability |
| Test driver | NumStabilityTest |

## Migration result

The declaration-bearing historical module was replaced by four structural
pieces:

- `Analysis.Norms.Core` owns the mechanically preserved residual norm
  implementation pending its Phase 11B semantic split;
- `Source.Higham.Chapter06.Theorem04` owns the exact source-shaped theorem
  tail;
- `Source.Higham.Chapter06` is the sorted declaration-free chapter aggregate;
  and
- `Analysis.Norms` is the declaration-free compatibility facade over Core and
  the theorem leaf.

All 23 historical production importers were retargeted to Core. `Analysis`
imports both canonical owners so its complete historical surface is
preserved, and `Source.Higham` imports the new Chapter 6 aggregate. No
production module imports the compatibility facade. Four isolated one-import
tests cover Core, Theorem 6.4, the Chapter 6 aggregate, and the historical
facade; the existing Analysis, Source, Higham, All, and root smokes cover the
updated entry points.

Core remains deliberately unclassified in Phase 11A. The source-tail seam is
reviewed, but the residual owner still interleaves reusable APIs and
source-shaped Chapter 6 developments. The zero reviewed-mixed count is
therefore inconclusive, not evidence that Core is already tier-uniform.

## Exact compiled ownership and dependency preservation

| Canonical owner | Total | Public | Internal | Private |
| --- | ---: | ---: | ---: | ---: |
| `Analysis.Norms.Core` | 1,783 | 1,385 | 394 | 4 |
| `Source.Higham.Chapter06.Theorem04` | 21 | 13 | 8 | 0 |
| **Moved family** | **1,804** | **1,398** | **402** | **4** |

The Phase 10F and Phase 11A dependency streams were compared after normalizing
only these two owners to historical owner `Analysis.Norms` and rewriting the
four generated Core-private prefixes back to their historical prefix. Public
and internal names, kinds, visibility, declaration multiplicity, and every
signature and body/proof edge match exactly. The normalized multiset
comparison reports zero missing, zero extra, and zero distinct delta records.

The global graph remains exactly 81,950 declarations, 305,425 signature
edges, 439,195 body/proof edges, and 491,557 union edges. The raw Phase 10F TSV
has SHA-256
`958CB3FFB9A7814A80B33E31B1A162E7F2E4E630FE025A48EA6330EC8438BF93`.
The raw Phase 11A TSV has SHA-256
`7FFBDD7F54F4DD19C0FCD5962D41A01A09ED55F6E251DB7F4240B42D340E6A09`.

## Immutable-map conformance

The implementation matches the frozen production tree, declaration split,
consumer retarget set, wrapper and aggregate surfaces, isolated-test plan,
tier treatment, and exact structural forecast. The measured result is 993
production modules and 4,069 direct imports, split into 2,700 internal and
1,369 external imports, exactly as mapped.

The map intentionally leaves the 1,783-constant Core unclassified and defers
its semantic leaves and remaining Chapter 6 source relocations. Independent
review recommended making that limitation more explicit; live tier and
architecture documentation was tightened accordingly without changing the
frozen map.

## Candidate-worktree Lean validation

| Command or gate | Result |
| --- | --- |
| Core, Theorem 6.4, Chapter 6, facade, Analysis, and Source.Higham focused build | passed; 4,203 jobs |
| Canonical, compatibility, and affected entry-point import surfaces | passed; 4,853 jobs |
| Comment/path correction focused rebuild | passed; 3,091 jobs |
| `lake build NumStability NumStabilityTest` run alone | passed; 5,247 jobs |
| `lake test` run alone | passed; 5,245 jobs |
| `lake env lean examples/LibraryLookup.lean` | passed |
| Representative axiom audit | passed; exactly `propext`, `Classical.choice`, and `Quot.sound` |
| Exact normalized Phase 10F/11A graph comparison | passed: zero missing and zero extra records |
| Strict-source architecture diagnostic | passed |

An initial accidental concurrent launch of the combined build and `lake test`
coincided with two Chapter 22 import-smoke subprocesses exiting without a Lean
source diagnostic. Both targets passed immediately when rerun separately
(3,406 and 3,405 jobs), and the complete combined build then passed when rerun
alone. This non-reproducing event is consistent with resource contention and
is retained here rather than being hidden as a successful first attempt.

## Architecture baseline

| Measure | Result |
| --- | ---: |
| Lean modules | 993 |
| Source lines | 1,468,449 |
| Nonblank source lines | 1,402,212 |
| Direct imports | 4,069 |
| Internal import edges | 2,700 |
| External imports | 1,369 |
| Import cycles | 0 |
| Classified modules | 384 |
| Classification coverage | 38.671% |
| Mixed modules | 0 |
| Uniquely owned declarations | 81,950 |
| Public declarations | 56,187 |
| Signature edges | 305,425 |
| Body/proof edges | 439,195 |
| Union edges | 491,557 |

The reviewed roles comprise 77 aggregates, 104 compatibility wrappers, two
internal modules, 58 reusable modules, 138 source modules, five upstream
modules, and zero reviewed mixed modules. There are zero direct or transitive
reusable-to-source or reusable-to-mixed paths.

The exact remaining inventory is 609 unclassified modules, 217 missing module
docstrings, and 403 historical naming exceptions. Partial classification
means the zero mixed count is a ratchet, not a repository-wide purity claim.

## Static validation

| Gate | Result |
| --- | --- |
| Layout, placeholder, test-reachability, and exact legacy-debt contract | passed: 993 modules |
| Classified source boundary | passed: zero forbidden direct or reachable paths |
| Compatibility contract | passed: 104 wrappers, 204 direct targets |
| Provenance contract | passed: 207 Apache files, five upstream modules |
| Aggregate structural and ordering contract | passed: 77 classified aggregates |
| Declaration-bearing umbrellas | passed: zero |
| Unsorted classified aggregates | passed: zero |
| Baseline reproducibility comparisons | passed with retained and freshly extracted TSVs |
| Independent production and test review | passed: no findings |
| Independent documentation and full-diff review | passed after corrections |
| `git diff --check` | passed |

## Review corrections

Independent production/test review verified the exact seam, the 33 preserved
Core imports, declaration-free sorted structural modules, the exact 23-module
consumer retarget set, and the isolated tests with no findings.

Documentation review found stale current-owner paths, brittle historical line
anchors, production comments that still named the facade, and an example that
still imported it. Current owner references and comments were retargeted,
historical Chapter 6 anchors were explicitly labeled as frozen pre-Phase-11A
positions, and the example now imports Core. The same review identified that
an unclassified Core makes the zero-mixed measurement inconclusive; README,
ARCHITECTURE, and TIERS now state that limitation directly.

## Clean-commit verification

The production tree at implementation revision
`63719a150fceecaa132f7c2ba5b57ba07e28bec7` was clean before the architecture
pair was captured. The following gates were repeated from committed source:

| Command or gate | Result |
| --- | --- |
| Initial `git status --short` | passed: no output |
| Focused owners, aggregates, facade, entry points, and import tests | passed; 4,853 jobs |
| `lake build NumStability` | passed; 4,789 jobs |
| `lake test` | passed; 5,244 jobs |
| `lake build NumStability NumStabilityTest` | passed; 5,247 jobs |
| `lake env lean examples/LibraryLookup.lean` | passed |
| Layout and exact legacy-debt contract | passed: 993 modules |
| Compatibility contract | passed: 104 wrappers, 204 direct targets |
| Provenance contract | passed: 207 Apache files, five upstream modules |
| Fresh declaration/dependency extraction | passed: 81,950 compiled declarations |
| Exact normalized Phase 10F/11A graph comparison | passed: zero missing and zero extra records |
| Clean strict-source baseline capture and reproducibility checks | passed |
| Representative axiom audit | passed at the established ceiling |

The generated baseline records `library_source_clean: true`, implementation
revision `63719a150fceecaa132f7c2ba5b57ba07e28bec7`, and normalized source-tree
digest `de93ad72a7b6d7b31d3deccade5e1b587fc34c6a43b62b0eda7ad32df72d9b9e`.

## Captured artifacts

- [Human-readable architecture baseline](2026-07-26-organization-phase11a.md)
- [Machine-readable architecture baseline](2026-07-26-organization-phase11a.json)
- [Phase 11A migration and ownership record](../migrations/2026-07-26-analysis-norms-source-tail-phase11a.md)

The source, import, declaration, toolchain, and Mathlib measurements were
reproduced before this evidence-only commit.
