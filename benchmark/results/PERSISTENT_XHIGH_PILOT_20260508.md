# Persistent GPT-5.5 xhigh Pilot, May 8 2026

This pilot tests the stronger solver protocol requested after the standard
pass@1 runs:

- `BENCHMARK_CODEX_MODEL=gpt-5.5`
- `BENCHMARK_CODEX_REASONING_EFFORT=xhigh`
- `BENCHMARK_SOLVER_PROMPT_VARIANT=persistent`
- `BENCHMARK_CODEX_TIMEOUT_SECONDS=1200`

The persistent prompt tells the solver that removing `sorry` is not enough: it
must continue resolving Lean errors and remaining placeholders until
`lake build BenchmarkTask` succeeds or the external timeout terminates the
attempt.

## Runs

### E01: LAPACK BERR backward-error certificate

Result root:
`benchmark/results/E01_LapackBerrBackward_gpt55_xhigh_persistent/20260508-021347`

Metrics:

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	124	1	yes	2026-05-07T23:14:22Z	2026-05-07T23:34:28Z	88	0	4	1	0
condition_c	0	0	no	2026-05-07T23:34:28Z	2026-05-07T23:39:40Z	74	142	136	0	0
```

Interpretation: this is a clean A-fail/C-pass result under the stronger
protocol.  Condition A spent the full 20-minute timeout and still left the
original proof placeholder.  Condition C solved the theorem in about five
minutes using the public library.

The public progress messages show the mechanism: Condition A identified the
missing floating-point residual-bound step but had no pre-proved residual
theorem available.  Condition C found the library residual theorem and then
completed the algebraic witness construction.

### E06: Oettli-Prager forward-error consequence

Result root:
`benchmark/results/E06_OettliPragerForward_gpt55_xhigh_persistent/20260508-024006`

Metrics:

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	0	no	2026-05-07T23:40:34Z	2026-05-07T23:44:09Z	45	153	147	0	0
condition_c	0	0	no	2026-05-07T23:44:09Z	2026-05-07T23:45:10Z	36	12	6	0	0
```

Interpretation: this is not a separator under the stronger protocol.  The full
library still helps substantially: Condition C closes the theorem by applying
`componentwise_forward_error_standard`, while Condition A rederives the finite
sum and absolute-value argument in 147 proof lines.  But because Condition A
passes, E06 should not be used as evidence that the library is necessary for
this theorem at GPT-5.5 xhigh persistence.

## Evidence Files

Each run archive contains:

- `BenchmarkTask.after.lean`: final solver-produced Lean file;
- `BenchmarkTask.diff`: exact proof-body diff from the canonical task;
- `validation.log`: validator reason for pass/fail;
- `agent_messages.md`: public solver progress and final messages;
- `codex_events.jsonl`: full structured event log;
- `attempt_metadata.md`: pinned model, effort, prompt variant, timeout, and
  environment controls.

Plots and aggregate metrics for this two-task pilot are in:

`benchmark/results/plots/persistent_xhigh_20260508/`

## Consequence

Persistent GPT-5.5 xhigh should be treated as a separate benchmark protocol,
not as a replacement for the standard pass@1 protocol.  It answers a different
question: whether a stronger, explicitly persistent agent can still fail under
Condition A while succeeding under Condition C.

E01 currently supports that claim.  E06 instead shows that some abstract
specification-transfer tasks are too algebraic and self-contained to separate
the conditions once the solver is strong enough.
