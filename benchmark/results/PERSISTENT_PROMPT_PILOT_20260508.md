# Persistent-Prompt Pilot: May 8, 2026

Draft status: benchmark result note.

This file records the first separate persistence-prompt benchmark run.  It
does not replace or invalidate the standard-prompt pass@1 runs from May 7.
It tests a different question: what happens when the solver is explicitly told
not to stop after one failed proof route, and the timeout is increased.

## Protocol Difference

Standard-prompt benchmark:

- prompt variant: `standard`
- timeout: 1200 seconds per condition
- interpretation: ordinary one-shot proof prompt, validated after the run

Persistent-prompt pilot:

- prompt variant: `persistent`
- timeout: 3600 seconds per condition
- extra instruction: keep revising against `lake build BenchmarkTask` until a
  local build succeeds or the external timeout stops the attempt

Both conditions still used byte-identical task files.  Condition A still had
only the bare stub environment; Condition C still had the public library
snapshot.

## E01 Persistent Pilot

- Task source: `benchmark/tasks/E01_LapackBerrBackward/Task.lean`
- Archived result root:
  `benchmark/results/E01_LapackBerrBackward_persistent/20260508-014020`
- Timeout: 3600 seconds per condition.

Outcome:

| Condition | Validation | Timeout | Public failure/success reason |
| --- | --- | --- | --- |
| Condition A | fail | no | Solver produced a long constructive perturbation proof but failed at the exact residual-rounding estimate that is absent from the bare stub. |
| Condition C | pass | no | Solver used the public library route and validated. |

Metrics:

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	1	no	2026-05-07T22:40:58Z	2026-05-07T22:49:28Z	91	147	141	0	0
condition_c	0	0	no	2026-05-07T22:49:28Z	2026-05-07T22:53:07Z	58	180	174	0	0
```

## Interpretation

The persistent prompt changed the Condition A failure mode.  In the standard
E01 run, Condition A left the original `sorry` and stopped after about four
minutes.  In this persistent run, Condition A spent longer, removed the
placeholder, and constructed explicit perturbations.  The final proof failed
where it needed the standard floating-point residual-computation estimate:

```lean
|b i - sum_j A i j * x j|
  <= |fl_residual fp n A x b i|
       + gamma fp (n + 1) * lapackBerrDenom n A x b i
```

That estimate is exactly the kind of stability infrastructure Condition A is
not given.  The attempt therefore gives stronger evidence than the standard
run for this task: under pressure and more time, Condition A did more useful
work but still did not reconstruct the missing floating-point residual-error
theorem from the bare definitions.

The run also shows that prompt pressure is not a formal guarantee of
persistence until timeout.  Condition A still stopped before the 3600-second
timeout after reaching what it described as the missing residual-rounding
estimate.  This should be reported honestly: the persistence prompt made the
model try harder, but it did not force indefinite search.

## Current Conclusion

For E01, the A/C separation survives the first persistence-prompt pilot:

- standard prompt: A failed by leaving `sorry`, C passed;
- persistent prompt: A failed with a non-building proof attempt at the missing
  residual-stability theorem, C passed.

This supports keeping the standard-prompt runs as Benchmark 1 and treating
persistent-prompt runs as a distinct Benchmark 2, not as a replacement.
