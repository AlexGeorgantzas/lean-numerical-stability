# Compensated-summation migration, phase 4B

Date: 2026-07-23

## Scope and rationale

This batch continues the staged split of
`NumStability.Algorithms.Summation.Compensated` after phase 4A. It extracts the
generic no-guard local correction API into the reusable compensated family and
moves two self-contained Higham equation (4.7) proof-route/counterexample
islands into the canonical Chapter 4 source hierarchy.

The migration was mapped from the phase-4A worktree markers rather than stale
pre-phase-4A line numbers. The strict-Sterbenz island began at
`correctionFormula_abs_order_not_imply_signed_sterbenz_exact_sum` and ended at
`correctionFormula_base2_abs_gt_inexact_not_imply_signed_sterbenz`. The generic
no-guard island began at `NoGuardCorrectionFormulaTrace` and ended at
`noGuardCorrectionFormulaTrace_model`. Its concrete source example began at
`noGuardCorrectionFormulaCounterexample` and ended at
`noGuardCorrectionFormulaCounterexample_toCorrectionFormulaTrace_not_exact`.

Base revision for the staged phase-4 worktree:
`312a970cddfb5c41da81237bb34b5cb5fd0c93e4`.

## Exact module map

| Previous owner | Canonical owner | Exact inclusive declaration range | Role |
| --- | --- | --- | --- |
| `Algorithms.Summation.Compensated` | `Source.Higham.Chapter04.Equation07.SterbenzCounterexamples` | `correctionFormula_abs_order_not_imply_signed_sterbenz_exact_sum` through `correctionFormula_base2_abs_gt_inexact_not_imply_signed_sterbenz` | source-specific failed strict-Sterbenz proof routes for equation (4.7) |
| `Algorithms.Summation.Compensated` | `Algorithms.Summation.Compensated.NoGuard.CorrectionFormula` | `NoGuardCorrectionFormulaTrace` through `noGuardCorrectionFormulaTrace_model` | reusable no-guard local trace and operation-witness API |
| `Algorithms.Summation.Compensated` | `Source.Higham.Chapter04.Equation07.NoGuardCounterexample` | `noGuardCorrectionFormulaCounterexample` through `noGuardCorrectionFormulaCounterexample_toCorrectionFormulaTrace_not_exact` | concrete equation-(4.7) no-guard counterexample |
| new source entry point | `Source.Higham.Chapter04.Equation07` | declaration-free imports of the two equation-(4.7) source leaves | source aggregate |
| `Source.Higham.Chapter04` | unchanged aggregate | adds `Source.Higham.Chapter04.Equation07` | Chapter 4 source entry point |
| `Algorithms.Summation.Compensated` path | unchanged transitional complete-family import | adds the reusable no-guard leaf and equation-(4.7) source umbrella | compatibility during the staged split |

All declarations remain in namespace `NumStability`. No declaration is
renamed, and no theorem statement or proof is changed.

## Dependency and compatibility contract

- `Algorithms.Summation.Compensated.NoGuard.CorrectionFormula` imports only
  `Analysis.Error` and the reusable correction-formula root. It does not import
  a Higham source module or the complete compensated family.
- `Equation07.SterbenzCounterexamples` imports finite-format arithmetic and
  source-local tactic support; the reusable FastTwoSum layer does not depend on
  it.
- `Equation07.NoGuardCounterexample` imports the reusable ordinary and
  no-guard correction APIs. Source modules may depend on reusable leaves; no
  reusable leaf imports a source module.
- `Equation07.lean` and `Chapter04.lean` are declaration-free source
  aggregates.
- The broad `Algorithms.Summation.Compensated` module imports the new leaves so
  its supported declaration surface remains unchanged during the staged
  migration.
- The abstract `correctionFormulaAbstractCounterexampleFPModel` block is not
  moved in this batch because later Kahan counterexamples still consume it.

## Isolated API checks

The batch adds and registers three canonical-only smoke modules:

- `NumStabilityTest.Import.SummationCompensatedNoGuardCorrectionFormula`;
- `NumStabilityTest.Import.Source.Chapter04.Equation07SterbenzCounterexamples`;
- `NumStabilityTest.Import.Source.Chapter04.Equation07NoGuardCounterexample`.

Each test imports one canonical leaf directly. The reusable test receives no
source module, and the source tests do not receive declarations through the
complete compensated umbrella.

## Targeted validation

The required targeted builds are:

```text
lake build NumStability.Algorithms.Summation.Compensated.NoGuard.CorrectionFormula
lake build NumStability.Source.Higham.Chapter04.Equation07.SterbenzCounterexamples
lake build NumStability.Source.Higham.Chapter04.Equation07.NoGuardCounterexample
lake build NumStability.Source.Higham.Chapter04.Equation07
lake build NumStability.Algorithms.Summation.Compensated
lake build NumStabilityTest.Import.SummationCompensatedNoGuardCorrectionFormula
lake build NumStabilityTest.Import.Source.Chapter04.Equation07SterbenzCounterexamples
lake build NumStabilityTest.Import.Source.Chapter04.Equation07NoGuardCounterexample
```

Observed results:

- the reusable no-guard leaf, both source leaves, and the declaration-free
  equation-(4.7) umbrella built successfully together (`1,478` jobs);
- the transitional compensated module and all three new isolated smoke tests
  built successfully together (`1,491` jobs);
- the Chapter 4 source aggregate and its entry-point smoke test built
  successfully together (`2,134` jobs).

The integrated Phase 4 worktree classifies the reusable no-guard leaf and the
Equation07 aggregate immediately. The architecture baseline and
complete-project gates are refreshed after the remaining compensated slices
are integrated.

## Deferred work

- the abstract equation-(4.7) counterexample model and its Kahan consumers;
- Kahan core, coefficient, finite-format, and error-bound layers;
- alternative and modified no-guard compensated algorithms;
- final conversion of `Algorithms.Summation.Compensated` to a declaration-free
  complete-family umbrella;
- final compatibility and baseline refresh for the integrated phase-4 batch.
