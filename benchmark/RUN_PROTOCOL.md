# Benchmark Run Protocol

Draft status: not finalized.

The benchmark is evaluated in generated workspaces, not directly in this source
tree.

## Source Tree Roles

- `benchmark/tasks/`: canonical task statements and task-spec notes.
- `benchmark/suites/`: task-list files used for plotting and batch planning.
- `benchmark/condition_a/`: generated-workspace Lake config template for the
  bare condition.
- `benchmark/condition_c/`: generated-workspace Lake config template for the
  full-library condition.  The generated package depends on a shared
  Condition C snapshot rather than copying the library into every attempt.
- `benchmark/stubs/<task>/`: optional task-specific generated-workspace source
  for the bare Condition A `LeanFpAnalysis.FP` module.
- `benchmark/stubs/common/`: default bare Condition A `LeanFpAnalysis.FP`
  provider used when a task has no task-specific stub. It defines only names
  needed by the benchmark theorem statements; it should not include stability
  theorems or gamma-calculus lemmas.
- `benchmark/scripts/`: helper scripts for generating workspaces.
- `docs/`, `README.md`, `examples/`: public library documentation allowed in
  Condition C.
- `thesis/DECISION_LOG.md`: project/thesis notes, never solver-facing.
- `.codex/`: local agent memory, never solver-facing.

## Generated Workspaces

Each run should create a fresh directory outside the repository, for example:

```text
/tmp/lean-fp-benchmark-runs/<run-id>/
  condition_a/T01_ScaledDot/
  condition_c/T01_ScaledDot/
```

Generated Condition A contains:

- `lakefile.toml`
- `lean-toolchain`
- Mathlib dependency
- the same task file used in Condition C, copied without edits
- a local bare `LeanFpAnalysis.FP` provider containing only the definitions
  required to state the theorem

Generated Condition A must not contain:

- the real `LeanFpAnalysis/` library
- proved library stability theorems such as `dotProduct_backward_error`,
  `matVec_backward_error`, `forwardSub_backward_error`, or
  `lu_solve_backward_error`
- proved gamma-calculus lemmas such as `gamma_mul`, `gamma_sum_le`, or
  `prod_error_bound`
- `docs/`
- `examples/`
- `benchmark/tasks/`
- `thesis/`
- `.codex/`
- previous attempts or solutions

Generated Condition C contains:

- `lakefile.toml`
- `lean-toolchain`
- the same task file used in Condition A, copied without edits
- a dependency path to the shared read-only Condition C snapshot
- symlinks to public library docs/source: `README.md`,
  `docs/LIBRARY_LOOKUP.md`, examples, and `public_library/`

The shared Condition C snapshot contains:

- `LeanFpAnalysis.lean` and `LeanFpAnalysis/`
- public library docs: `README.md`, `docs/LIBRARY_LOOKUP.md`, examples
- Lake files needed to build the public library

Generated Condition C must not contain:

- `.codex/`
- `thesis/DECISION_LOG.md`
- benchmark task-spec notes
- previous attempts or solutions
- any reference proof files

The shared Condition C snapshot must not contain:

- `.codex/`
- `.claude/`
- `benchmark/`
- `thesis/`
- previous attempts or solutions

## Solver-Facing Task Rule

For each task, Condition A and Condition C should receive byte-identical copies
of the task file.  The task file should normally import `LeanFpAnalysis.FP` in
both conditions.  In Condition A this module name is supplied by a generated
bare stub with just enough definitions to state the theorem; in Condition C it
is supplied by the actual library.

The solver-facing task file should contain:

- imports;
- task-local definitions needed by the theorem;
- exactly one theorem whose proof body is `sorry`;
- no proof strategy comments;
- no expected theorem names to apply;
- no task rationale.

## Validation

Before running an agent attempt, the generated task package should build with
`sorry` allowed:

```bash
lake build BenchmarkTask
```

This is called a preflight build.  It only means the generated package,
imports, definitions, and theorem statement are coherent enough for Lean to
compile.  It does not mean the theorem has been proved.

After an agent attempt:

- run `lake build`;
- reject if any `sorry`, `admit`, `sorryAx`, new `axiom`, or weakened theorem
  remains;
- reject if imports, task-local definitions, namespaces, or the theorem
  statement changed;
- record build result, diff, proof lines, and failure reason.

For the current local harness, run a full one-task attempt with:

```bash
benchmark/scripts/setup_shared_lake_packages.sh
benchmark/scripts/setup_condition_c_snapshot.sh
BENCHMARK_CODEX_TIMEOUT_SECONDS=1200 benchmark/scripts/run_task_once.sh T01_ScaledDot
```

For the external-source pilot suite, use task names from:

```text
benchmark/suites/external_stability.tsv
```

For example:

```bash
BENCHMARK_CODEX_TIMEOUT_SECONDS=1200 benchmark/scripts/run_task_once.sh E01_LapackBerrBackward
```

`prepare_solver_run.sh` creates both condition workspaces, writes a neutral
solver prompt, records metadata, checks task hashes, and runs the preflight
builds.  Generated workspaces use a shared third-party Lake package cache under
`~/.cache/lean-fp-analysis/lake-packages/...` by default.  This keeps Mathlib
and other Lake dependencies reusable across generated workspaces without giving
the solver a symlink back to the project repository.  The shared cache contains
third-party packages only, not benchmark notes, thesis notes, memory files,
previous attempts, or `LeanFpAnalysis` source.
`setup_condition_c_snapshot.sh` creates a shared read-only snapshot of the
public library for Condition C.  Condition C task workspaces depend on this
snapshot through Lake and expose it through symlinks for inspection, but solver
edits still happen in a fresh per-attempt task workspace.

The manual GitHub Actions workflow `.github/workflows/benchmark_cloud.yml`
runs the expensive snapshot and preflight steps on a hosted runner and uploads
the archived preflight metadata as an artifact.  Solver attempts are kept out
of that workflow until Codex authentication for a non-local runner is chosen.
`run_codex_attempt.sh` invokes a fresh non-interactive Codex process with
ephemeral session storage and archives the attempt under
`benchmark/results/<task>/<timestamp>/<condition>/`, where generated run ids
have the form `<task>-YYYYMMDD-HHMMSS`.  It runs Codex with a temporary
auth-only `CODEX_HOME`, a temporary `HOME`, and a temporary `XDG_CACHE_HOME`.
It passes the host `ELAN_HOME` only so the already installed Lean toolchain is
available without forcing Elan to download into the temporary home.  It also
places a workspace-local `lake` wrapper first on `PATH`.  The wrapper supports
the solver-requested `lake build BenchmarkTask` command by invoking `lean`
directly with the `LEAN_PATH` computed by Lake during preflight.  This gives
the solver real Lean feedback on `BenchmarkTask.lean` without letting Lake
write lock files inside an external package cache.  Post-run validation still
uses the real Lake build, not this wrapper.  The runner also adds only the
shared third-party Lake package cache as an explicit Codex directory, so
tooling can inspect/reuse prebuilt Mathlib dependencies without granting
Condition A access to the full `LeanFpAnalysis` snapshot.  It disables plugin
and memory features, ignores user configuration and rules, enforces a
process-group timeout
(`BENCHMARK_CODEX_TIMEOUT_SECONDS`, default 1200) through
`run_with_timeout.py`, and removes the temporary home after the attempt.
`validate_attempt.sh` is the post-attempt validator: it rejects changes outside
the theorem proof body, remaining placeholders, forbidden declarations, and
build failures.  `cleanup_run_workspaces.sh` removes temporary run workspaces
after results have been archived.

Every condition archive contains the final solver output
`BenchmarkTask.after.lean`, the canonical task file, a diff, validation log,
solver event log, extracted public solver messages, final solver message,
workspace file list, exit codes, and attempt metadata.  These files are the
evidence used to decide whether a failure is a real failed proof, a harness
issue, or an invalid attempt.  The extracted public messages are useful audit
context, but they are not hidden chain-of-thought.

`run_task_once.sh` is the preferred local entrypoint.  It prepares fresh
Condition A and Condition C workspaces for one task, archives preflight
metadata, runs both solver attempts with the same timeout, validates each
attempt, writes `RUN_ANALYSIS.md` and `metrics.tsv`, then removes the temporary
workspaces.

`analyze_run.sh` writes a compact post-run analysis under the archived result
root.  The metrics table records, per condition:

- Codex exit code;
- validation exit code;
- timeout marker;
- start and finish timestamps;
- Codex event-log line count;
- diff line count;
- proof-line count;
- remaining placeholder count;
- forbidden declaration count.
- mechanical validation classification.

It also writes `agent_messages.md` for each condition by extracting public
`agent_message` events from `codex_events.jsonl`.

`plot_pass_at_1.py` accepts either the old built-in prototype task list or an
explicit task-list file.  For the external-source suite:

```bash
python3 benchmark/scripts/plot_pass_at_1.py \
  --task-list benchmark/suites/external_stability.tsv \
  --date-prefix YYYYMMDD \
  --output-dir benchmark/results/plots/pass_at_1_YYYYMMDD_external
```
