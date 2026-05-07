# Solver Trace Summary: 2026-05-05 Pass@1

This document audits the saved solver outputs for the corrected pass@1 run.

The produced Lean files are saved.  Across all archived benchmark runs there
are currently 38 `BenchmarkTask.after.lean` files.  The corrected 2026-05-05
pass@1 batch includes one saved `BenchmarkTask.after.lean` for each task and
condition.

The harness also saves `codex_events.jsonl`.  That file records public solver
messages, tool calls, command output, and file-change events.  It does not
contain hidden chain-of-thought.  We can audit the solver's public progress
messages and command trace, but we should not describe that as private
reasoning.

## What Is Saved Per Condition

For each `benchmark/results/<task>/<timestamp>/<condition>/` directory:

- `BenchmarkTask.after.lean`: final Lean artifact submitted by the solver.
- `BenchmarkTask.diff`: diff against the canonical task.
- `validation.log`: post-attempt Lean validation.
- `codex_events.jsonl`: public event log.
- `agent_messages.md`: public solver messages extracted from the event log.
- `codex_last_message.txt`: final public solver message.
- `attempt_metadata.md`: command, timeout, commit, and exit metadata.
- `workspace_files.txt`: files left in the solver workspace.

This is enough to distinguish these cases:

- the solver did not edit the theorem and left `sorry`;
- the solver edited the proof but the final Lean file did not build;
- the solver tried a forbidden escape hatch such as `sorryAx`;
- the solver changed the theorem interface;
- the solver passed validation.

## Latest Corrected Condition A Attempts

| Task | Saved Lean output | Mechanical rejection | Trace-level diagnosis |
| --- | --- | --- | --- |
| T01_ScaledDot | `benchmark/results/T01_ScaledDot/20260505-195836/condition_a/BenchmarkTask.after.lean` | Placeholder remained. | The solver found only bare definitions and reported that proving the theorem would require a theorem-local dot-product induction plus gamma algebra. No final proof edit was kept. |
| T02_ShiftedDot | `benchmark/results/T02_ShiftedDot/20260505-200758/condition_a/BenchmarkTask.after.lean` | Final Lean file did not build. | The solver attempted a proof using local FP definitions and automation. Validation failed with unsolved `grind` goals around the shifted-dot absolute-value bound. |
| T03_ResidualCertificate | `benchmark/results/T03_ResidualCertificate/20260505-202047/condition_a/BenchmarkTask.after.lean` | Final Lean file did not build. | The solver reduced the task to the missing residual-error theorem. Validation failed on an unproved bound relating exact residual and `fl_residual`, plus an invalid `abs_add` identifier. |
| T04_ForwardSubResidual | `benchmark/results/T04_ForwardSubResidual/20260505-222035/condition_a/BenchmarkTask.after.lean` | Placeholder remained. | The solver did not find a theorem-local route to triangular-solve backward error from the bare algorithm definitions and restored the original `sorry`. |
| T05_Gemv | `benchmark/results/T05_Gemv/20260505-203449/condition_a/BenchmarkTask.after.lean` | Placeholder remained. | The solver identified the need to construct a full GEMV perturbation through `Fin.foldl` and gamma absorption from primitive FP axioms, then restored the original `sorry`. |
| T06_TriangularSolveSingle | `benchmark/results/T06_TriangularSolveSingle/20260505-222838/condition_a/BenchmarkTask.after.lean` | Final Lean file did not build. | The solver tried simple witnesses and automation. Validation failed because Lean could not synthesize/prove the existential combined perturbation theorem. |
| T07_LUSolveGrowth | `benchmark/results/T07_LUSolveGrowth/20260505-230936/condition_a/BenchmarkTask.after.lean` | Final Lean file did not build. | The solver tried `DeltaA = Lhat*Uhat - A`. That proves only the LU factorization discrepancy bound; validation failed at the final equation for the computed `fl_forwardSub`/`fl_backSub` solution. |
| T08_CholeskySolveGrowth | `benchmark/results/T08_CholeskySolveGrowth/20260505-225058/condition_a/BenchmarkTask.after.lean` | Placeholder remained. | The solver claimed a counterexample based on `fl_forwardSub` processing rows in descending order. That diagnosis is not accepted as-is: the current stub definition starts with row `0` when `n = 2`. The mechanical reason for rejection is simply that the final file still contained `sorry`. |
| T09_OneStepRefinement | `benchmark/results/T09_OneStepRefinement/20260505-205939/condition_a/BenchmarkTask.after.lean` | Placeholder remained. | The solver identified the missing conventional residual-error lemma as the blocker and left the original theorem unproved. |
| T10_StationaryForwardSub | `benchmark/results/T10_StationaryForwardSub/20260505-225743/condition_a/BenchmarkTask.after.lean` | Placeholder remained. | The solver found the route that exists in the full library, namely `forwardSub_backward_error` plus `normwise_residual_bound`, but those lemmas are deliberately absent from Condition A. |

## Latest Corrected Condition C Attempts

All ten matching Condition C attempts passed validation:

- `benchmark/results/T01_ScaledDot/20260505-195836/condition_c/BenchmarkTask.after.lean`
- `benchmark/results/T02_ShiftedDot/20260505-200758/condition_c/BenchmarkTask.after.lean`
- `benchmark/results/T03_ResidualCertificate/20260505-202047/condition_c/BenchmarkTask.after.lean`
- `benchmark/results/T04_ForwardSubResidual/20260505-222035/condition_c/BenchmarkTask.after.lean`
- `benchmark/results/T05_Gemv/20260505-203449/condition_c/BenchmarkTask.after.lean`
- `benchmark/results/T06_TriangularSolveSingle/20260505-222838/condition_c/BenchmarkTask.after.lean`
- `benchmark/results/T07_LUSolveGrowth/20260505-230936/condition_c/BenchmarkTask.after.lean`
- `benchmark/results/T08_CholeskySolveGrowth/20260505-225058/condition_c/BenchmarkTask.after.lean`
- `benchmark/results/T09_OneStepRefinement/20260505-205939/condition_c/BenchmarkTask.after.lean`
- `benchmark/results/T10_StationaryForwardSub/20260505-225743/condition_c/BenchmarkTask.after.lean`

The Condition C files should be inspected before thesis reporting to classify
whether each proof is a direct library theorem application, a short
composition, or a larger proof script.

The current inspection gives this provisional classification:

| Task | Condition C proof shape |
| --- | --- |
| T01_ScaledDot | Short composition of `dotProduct_backward_error`, `FPModel.model_mul`, and `gamma_mul`. |
| T02_ShiftedDot | Short-to-medium composition of dot-product backward error, `FPModel.model_add`, and gamma/absolute-value algebra. |
| T03_ResidualCertificate | Direct use of `conventional_residual_error` plus triangle inequality. |
| T04_ForwardSubResidual | Direct use of `forwardSub_backward_error` plus residual rearrangement. |
| T05_Gemv | Larger theorem-local composition: row dot-product backward errors, two multiplications, final addition, and gamma absorption. |
| T06_TriangularSolveSingle | Larger theorem-local composition of `forwardSub_backward_error` and `backSub_backward_error`; manually expands the single `DeltaA`. |
| T07_LUSolveGrowth | Direct use of `banded_lu_solve_backward_stable` plus a coefficient rewrite. |
| T08_CholeskySolveGrowth | Direct use of `cholesky_solve_backward_error` plus the task-local growth hypothesis. |
| T09_OneStepRefinement | Direct use of `conventional_residual_error` and `one_step_residual_bound`. |
| T10_StationaryForwardSub | Bridge proof: constructs `ComputedIteration`, derives local-error norm bound from `forwardSub_backward_error`, then applies `normwise_residual_bound`. |

## Caveat: Solver-Internal Build Friction

Several Condition A public messages mention Lake failing to write lock files
under the shared cached Mathlib package directory.  Final validation still ran
and produced mechanical pass/fail results, so the archived rejection is valid:
the submitted Lean artifact either did not build or still contained a proof
placeholder.

However, this is a real protocol caveat.  If the solver spends time debugging
workspace package permissions, the result measures both missing library
infrastructure and harness friction.  Before final thesis-grade runs, generated
workspaces should give the solver a clean writable Lake package/build area or
an equivalent no-lock validation path, while still sharing immutable build
artifacts where possible to avoid disk blow-up.

## Conclusion From This Audit

The Condition A failures are valid pass@1 failures under the current mechanical
validator.  They should not be overinterpreted as "the theorem is impossible
without the library."  The stronger and fairer claim is:

Under the corrected pass@1 protocol, a fresh solver produced no accepted Lean
proofs in Condition A and accepted Lean proofs for all ten tasks in Condition C.
The archived outputs show that Condition A failures were mainly due to missing
formal stability lemmas, with some additional workspace-build friction that
should be removed before final benchmark runs.
