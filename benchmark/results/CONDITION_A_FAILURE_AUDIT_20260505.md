# Condition A Failure Audit: 2026-05-05 Pass@1

This audit explains why the corrected Condition A pass@1 result is counted as
`0/10`.

The benchmark does not count a Condition A attempt as a failure merely because
the file originally contained `sorry`.  Every attempt is archived after Codex
has run.  The archived `BenchmarkTask.after.lean` file is then validated by
Lean under the generated Condition A workspace.

For each condition and task, the harness saves:

- `BenchmarkTask.after.lean`: final Lean file produced by the solver;
- `BenchmarkTask.diff`: diff against the canonical task file;
- `validation.log`: full post-attempt Lean validation log;
- `codex_events.jsonl`: solver event log;
- `agent_messages.md`: public solver progress/final messages extracted from
  `codex_events.jsonl`;
- `codex_last_message.txt`: final solver message;
- `attempt_metadata.md`: command, timeout, commit, and exit-code metadata;
- `metrics.tsv` and `RUN_ANALYSIS.md`: compact run-level analysis.

The validator rejects an attempt only for mechanical reasons:

- the theorem interface changed before the proof body;
- a proof placeholder remained: `sorry`, `admit`, or `sorryAx`;
- a new forbidden declaration appeared: `axiom`, `opaque`, or `unsafe`;
- the final `BenchmarkTask.lean` did not build;
- the Condition C snapshot was mutated.

Thus a Condition A rejection is not a subjective judgment that the proof was
"bad".  It means the final submitted Lean artifact did not constitute a proof
of the original theorem.

## Corrected Audited Runs

| Task | Run | Archived output | Condition A classification |
| --- | --- | --- | --- |
| T01_ScaledDot | `20260505-195836` | `benchmark/results/T01_ScaledDot/20260505-195836/condition_a/BenchmarkTask.after.lean` | Proof placeholder remained. |
| T02_ShiftedDot | `20260505-200758` | `benchmark/results/T02_ShiftedDot/20260505-200758/condition_a/BenchmarkTask.after.lean` | Final Lean file did not build. |
| T03_ResidualCertificate | `20260505-202047` | `benchmark/results/T03_ResidualCertificate/20260505-202047/condition_a/BenchmarkTask.after.lean` | Final Lean file did not build. |
| T04_ForwardSubResidual | `20260505-222035` | `benchmark/results/T04_ForwardSubResidual/20260505-222035/condition_a/BenchmarkTask.after.lean` | Proof placeholder remained. |
| T05_Gemv | `20260505-203449` | `benchmark/results/T05_Gemv/20260505-203449/condition_a/BenchmarkTask.after.lean` | Proof placeholder remained. |
| T06_TriangularSolveSingle | `20260505-222838` | `benchmark/results/T06_TriangularSolveSingle/20260505-222838/condition_a/BenchmarkTask.after.lean` | Final Lean file did not build. |
| T07_LUSolveGrowth | `20260505-230936` | `benchmark/results/T07_LUSolveGrowth/20260505-230936/condition_a/BenchmarkTask.after.lean` | Final Lean file did not build. |
| T08_CholeskySolveGrowth | `20260505-225058` | `benchmark/results/T08_CholeskySolveGrowth/20260505-225058/condition_a/BenchmarkTask.after.lean` | Proof placeholder remained. |
| T09_OneStepRefinement | `20260505-205939` | `benchmark/results/T09_OneStepRefinement/20260505-205939/condition_a/BenchmarkTask.after.lean` | Proof placeholder remained. |
| T10_StationaryForwardSub | `20260505-225743` | `benchmark/results/T10_StationaryForwardSub/20260505-225743/condition_a/BenchmarkTask.after.lean` | Proof placeholder remained. |

## Interpretation

The corrected Condition A failures are valid pass@1 failures under the current
protocol.  They show that, in one attempt per task, the fresh solver did not
produce a Lean proof from Mathlib plus the bare theorem-statement stubs.

They do not prove a universal impossibility result.  A different prompt,
longer timeout, repeated attempts, or a stronger model might solve some
Condition A tasks.  The thesis claim should therefore be phrased as an
empirical pass@1 result under this protocol, with pass@k and repeated trials as
future or follow-up measurements.

The failure modes are also useful evidence:

- Some attempts left the theorem `sorry` unchanged, meaning the solver did not
  find a viable route.
- Some attempts edited the proof but Lean reported unsolved goals, unknown
  tactics, or missing reasoning steps.
- The two earlier invalid Condition A passes, T07 via `sorryAx` and T10 via a
  degenerate norm stub, were removed from the corrected table and the harness
  was patched.

This is why the current audited result is stronger than simply checking whether
the initial task file still built with `sorry`.

For a deeper trace-level audit of what the solver attempted in each rejected
Condition A run, see
`benchmark/results/SOLVER_TRACE_SUMMARY_20260505.md`.
