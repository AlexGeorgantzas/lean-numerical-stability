# Insertion-summation semantic migration, phase 3

Date: 2026-07-23

## Scope and rationale

This batch splits the remaining mixed insertion-summation module along
contiguous dependency boundaries. It preserves every declaration name and the
complete behavior of both the canonical family import and the historical
root-level compatibility import.

Before this migration, `Algorithms.Summation.Insertion` combined five reusable
concerns with two concrete examples from Higham Chapter 4, Section 4.1. The
concrete examples formed a one-way tail: no reusable declaration depended on
them, and the recursive, pairwise, and balanced-tree imports were used only by
that tail.

`Algorithms.Summation.Compensated` remains outside this batch. Its reusable
Kahan analysis and source-specific equations, counterexamples, and corrections
are interleaved; it requires a staged migration of its own.

## Exact module map

| Previous owner | Canonical owner | Role and scope |
| --- | --- | --- |
| `Algorithms.Summation.Insertion`, active-list definitions and insertion ordering lemmas | `Algorithms.Summation.Insertion.ActiveList` | reusable active-list invariant and ordered insertion |
| same, direct list loop through `fl_insertionSumList` | `Algorithms.Summation.Insertion.Executor` | reusable rounded list executor and termination API |
| same, `InsertionScheduleTree` through its exact-cost and greedy-optimality results | `Algorithms.Summation.Insertion.Schedule` | reusable abstract schedules and optimality proof engine |
| same, `SumTree` exact-unit-roundoff bridges | `Algorithms.Summation.Insertion.RunningError` | reusable running-error/merge-cost bridge |
| same, schedule-item executor and end-to-end schedule witnesses | `Algorithms.Summation.Insertion.ScheduleExecution` | reusable correspondence between the list executor and schedule certificates |
| same, the `1,2,4,8` and near-one four-entry examples and their error corollaries | `Source.Higham.Chapter04.Section01.InsertionExamples` | source correspondence |
| `Algorithms.Summation.Insertion` path | unchanged declaration-free family umbrella | complete aggregate over all five reusable leaves and the source leaf |

The large exchange/contraction engine remains together in `Schedule`. Private
helpers declared in its middle are used thousands of lines later, so a finer
`Optimality` split is deliberately deferred until its declaration dependency
graph is reviewed separately.

## Import and compatibility contract

- `Algorithms.HighamChapter4KaoWangScope` imports `Insertion.RunningError`,
  the narrow layer containing the schedule cost bridge it uses.
- `Algorithms.OrderingExamples` imports `Insertion.ActiveList`, the narrow
  ordered-list layer it uses.
- `Algorithms.Summation` continues to import the complete `Insertion`
  family umbrella.
- `Algorithms.InsertionSum` remains an import-only compatibility wrapper
  targeting that complete umbrella. Its removal policy is unchanged: removal
  requires an announced breaking release.
- `Source.Higham.Chapter04.Section01` imports the new source leaf.

No declaration is renamed, no namespace changes, and no compatibility path is
removed.

## Isolated API checks

The batch adds separate smoke modules for:

- `Insertion.ActiveList`;
- `Insertion.Executor`;
- `Insertion.Schedule`;
- `Insertion.RunningError`;
- `Insertion.ScheduleExecution`;
- the complete `Insertion` family umbrella; and
- `Source.Higham.Chapter04.Section01.InsertionExamples`.

The existing old-only `Algorithms.InsertionSum` test will check both a reusable
declaration and a source declaration, ensuring that no unrelated sibling import
can hide a broken wrapper. Chapter 4 and complete summation entry-point tests
will also check the new source surface.

## Validation evidence

- Every reusable leaf, the source leaf, the complete family, and the historical
  wrapper compiled through isolated smoke modules.
- The focused insertion, source, consumer, family, and compatibility build
  passed with 3,174 jobs.
- `lake test` passed all 4,770 jobs, and
  `lake build NumStability NumStabilityTest` passed all 4,772 jobs.
- The declaration-bearing architecture build passed all 4,653 jobs; compiled
  declaration extraction and the no-build reproducibility check both passed.
- The compiled public-declaration count remains 56,186, unchanged from the
  Phase 2 baseline.
- Layout, compatibility, provenance, strict source-boundary, aggregate-order,
  normalization, Python-compilation, and `git diff --check` gates passed.

The tightened tier and layout manifests classify all five reusable leaves and
the source leaf while retaining the declaration-free family aggregate. The
reviewed mixed queue is reduced from two modules to one, with 652 modules still
explicitly unclassified. The captured graph has 785 Lean modules, no import
cycles, and no direct or transitive path from a classified reusable module to
a source or mixed module.

See the [Phase 3 baseline](../baselines/2026-07-23-organization-phase3.md)
and [build evidence](../baselines/2026-07-23-organization-phase3-build.md) for
the complete measurements and interpretation guardrails.
