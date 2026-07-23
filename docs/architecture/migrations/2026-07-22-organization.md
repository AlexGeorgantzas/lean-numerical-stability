# Repository organization phase 1

## Status and scope

This record describes the first enforceable organization phase, developed on
`codex/organize-repository` from
`11a5241c7496851a8653080f30d39182c4eeb4d4`. The declaration baseline was
captured before the candidate worktree was committed; the implementation
revision is the commit containing this record.

This phase establishes a Mathlib-style direction without claiming that the
entire 1.46-million-line library has already completed that migration. It
contains these coordinated slices:

1. documented public entry points, semantic tiers, naming rules, compatibility
   policy, architecture contracts, and CI ratchets;
2. canonical source-correspondence trees for Higham Chapters 14, 24, and 25,
   with import-only compatibility wrappers at every historical path;
3. a reusable `Algorithms.LinearSystems.Triangular` family with semantic leaf
   names and a complete family umbrella;
4. a complete `Algorithms.Sylvester` umbrella, replacing 28 leaf imports in
   the Algorithms aggregate with one family import;
5. extraction of reusable summation-sign mathematics into
   `Analysis.Summation.Signs`, with mixed error-bound material isolated in
   `Analysis.Summation.ErrorBounds` and the old path retained as an aggregate;
6. reproducible architecture baselines, aggregate sorting, provenance and
   licensing checks, contribution guidance, test-driver wiring, and repository
   hygiene.

The detailed path maps and dependency rationales are recorded in the sibling
Chapter 14, Chapter 24, Chapter 25, triangular, Sylvester, and summation
migration records.

## Resulting architecture snapshot

The final declaration-bearing baseline for this candidate is
[`../baselines/2026-07-22-organization-final.md`](../baselines/2026-07-22-organization-final.md),
with its complete machine-readable form in
[`../baselines/2026-07-22-organization-final.json`](../baselines/2026-07-22-organization-final.json).

| Measure | Result |
| --- | ---: |
| Lean modules | 772 |
| Physical Lean lines | 1,465,427 |
| Direct imports | 3,392 |
| Internal direct-import edges | 2,126 |
| External direct imports | 1,266 |
| Unresolved project imports | 0 |
| Import cycles | 0 |
| Classified modules | 120 |
| Unclassified modules | 652 |
| Classification coverage | 15.544% |
| Mixed modules | 9 |
| Modules missing module docs | 227 |
| Naming exceptions | 456 |
| Declaration-bearing umbrellas | 1 |
| Unsorted import-only aggregates | 0 |

The compiled graph owns 81,893 declarations, of which 56,186 are public. It
contains 305,416 signature-reference edges and 439,174 body/proof-reference
edges. Those figures are descriptive baselines, not quality targets.

The historical `NumStability.Algorithms` aggregate now has 463 direct imports,
down from 490 immediately before the Sylvester umbrella. Narrow canonical
imports remain the policy for implementation modules; broad aggregates exist
for user discovery and compatibility.

## Compatibility and provenance

The compatibility manifest covers 43 forwarding modules and 44 canonical
targets. All migrated declarations retain their established names and
namespaces. Historical imports remain supported until a declared breaking
release; this phase does not delete them or silently redirect consumers through
chains of wrappers.

The provenance gate recognizes 148 Apache-marked production files and five
evidenced upstream modules. The full Apache-2.0 license text, adapted-module
notices, and source references are recorded in the repository rather than left
as scattered file-header claims.

## Verification

The following evidence was collected after the candidate Lean graph was frozen:

- `lake test` completed successfully: `NumStabilityTest` built all 4,741 jobs,
  including the root, `All`, `Source`, historical `Higham`, Algorithms,
  canonical-only, and isolated historical-only import tests.
- The full baseline generator completed the `NumStability` build at 4,641 jobs
  and successfully extracted the compiled declaration graph.
- `check_layout.py` accepted the exact debt baseline at 772 modules, with 652
  unclassified, 9 mixed, 227 missing module docs, 456 naming exceptions, one
  declaration-bearing umbrella, and zero unsorted aggregates.
- `check_compatibility.py` accepted 43 wrappers covering 44 canonical targets.
- `check_provenance.py` accepted all 148 Apache-marked files and five evidenced
  upstream modules.
- The strict source check found zero direct or transitive classified
  reusable-to-source and reusable-to-mixed paths.
- The Apache notice normalizer and aggregate-import sorter both reported clean
  dry runs; all architecture Python tools compiled; `git diff --check` passed.

The companion command-level record is
[`../baselines/2026-07-22-organization-build.md`](../baselines/2026-07-22-organization-build.md).

## Deferred debt

This is not the end of the repository migration. The following are explicit,
ratcheted work queues:

- 652 modules are not yet assigned a reviewed semantic tier;
- 9 modules still combine reusable and source-specific material;
- 227 modules still lack a module docstring;
- 456 historical names still violate the canonical naming policy;
- `NumStability.Algorithms.FastMatMul` is still a declaration-bearing umbrella;
- several files remain giant proof monoliths, led by `HighamChapter11`
  (137,119 lines), `HighamChapter9` (113,808), and `LeastSquares.LSE`
  (106,600);
- the physical source-target gate remains false because classification is
  incomplete and mixed modules remain;
- existing Lean linter and deprecation warnings are recorded build debt, not
  silently treated as resolved by this path migration.

Zero forbidden paths among classified modules is therefore a meaningful local
boundary result, but not proof of complete repository-wide separation.

## Required continuation order

Further organization should proceed in this order:

1. classify one dependency-contained family at a time and lower the exact debt
   baseline in the same change;
2. split mixed modules at declaration-level dependency seams;
3. introduce semantic canonical paths and preserve old paths as documented,
   isolated compatibility wrappers;
4. split giant files only after compiled declaration dependencies identify
   stable seams;
5. remove wrappers only in a declared breaking release after downstream
   migration evidence exists.

This order keeps every intermediate revision buildable, reviewable, and
backward compatible.
