# Summation semantic-boundary migration, phase 2

Date: 2026-07-23

## Scope

This batch resolves the low-risk source/reusable seams in the summation family
without renaming declarations or removing published imports.

| Previous owner | Canonical owner | Role |
| --- | --- | --- |
| `Algorithms.Summation.Recursive` generic declarations | `Algorithms.Summation.Recursive.Core` | reusable |
| `Algorithms.Summation.Recursive` Problem 4.3 declarations | `Source.Higham.Chapter04.Problem03` | source |
| `Algorithms.Summation.Pairwise` generic declarations | `Algorithms.Summation.Pairwise.Core` | reusable |
| six-term Higham §4.1 schedule | `Source.Higham.Chapter04.Section01.PairwiseSixTerm` | source |
| `Algorithms.Summation.Tree.RecursiveBridge` declarations | `Algorithms.Summation.Tree.Chain` | reusable |
| `Algorithms.Summation.Tree.RecursiveBridge` path | forwarding import to `Tree.Chain` | compatibility |

The `Recursive` and `Pairwise` paths remain declaration-free complete family
umbrellas, so existing imports retain both their generic and source-facing
surfaces. Historical root-level wrappers continue to target those umbrellas.

## Reviewed classifications

`Accumulator`, `DoublyCompensated`, `PlusMinus`, and
`Analysis.Summation.ErrorBounds` are source-independent despite carrying
provenance citations and are now classified reusable. `Compensated` and
`Insertion` remain the only reviewed mixed summation modules; their large
source clusters require separate dependency-contained migrations.

The reusable classification of `Analysis.Summation.ErrorBounds` supersedes its
transitional mixed classification in the 2026-07-22 organization record. Its
declarations depend on the floating-point model and reusable summation APIs,
not on source-owned Chapter 4 declarations.

The executable layout ratchet after the change records 779 Lean modules, 652
unclassified modules, 2 mixed modules, 227 missing module docstrings, 455
legacy naming exceptions, one declaration-bearing umbrella, and no unsorted
aggregate imports.

## Compatibility and tests

The change adds isolated imports for both reusable cores, both complete family
umbrellas, the chain-tree leaf, the complete summation aggregate, the Chapter 4
source umbrella, and the historical recursive-tree bridge. Existing historical
recursive, pairwise, and tree wrapper tests now check declarations from the
moved surfaces as well.

No declaration was renamed and no forwarding path was removed.

Production imports were narrowed to match the new ownership boundaries:

- `Accumulator`, `Compensated`, `Insertion`, `PlusMinus`,
  `OrderingExamples`, and `WilkinsonAttainability` now consume
  `Summation.Recursive.Core` directly;
- `NeumaierCompensatedFiniteFormat` imports `Summation.Recursive.Core`
  explicitly instead of receiving it through a source-bearing family path;
- `Insertion` consumes `Summation.Pairwise.Core` directly; and
- `BunchTridiagonalSparseSolveCh11Closure` consumes `Summation.Tree.Chain`
  instead of the historical `Tree.RecursiveBridge` path.

## Evidence

The final verification record for the batch is captured in
`docs/architecture/baselines/2026-07-23-organization-phase2-build.md`, and the
graph snapshot is captured in both machine-readable and review-oriented forms:
`docs/architecture/baselines/2026-07-23-organization-phase2.json` and
`docs/architecture/baselines/2026-07-23-organization-phase2.md`.
