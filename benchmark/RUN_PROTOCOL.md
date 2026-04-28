# Benchmark Run Protocol

Draft status: not finalized.

The benchmark is evaluated in generated workspaces, not directly in this source
tree.

## Source Tree Roles

- `benchmark/tasks/`: canonical task statements and task-spec notes.
- `benchmark/condition_a/`: template Lake config for the bare condition.
- `benchmark/condition_c/`: template Lake config for the full-library
  condition.
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
- `docs/`
- `examples/`
- `benchmark/tasks/`
- `thesis/`
- `.codex/`
- previous attempts or solutions

Generated Condition C contains:

- `lakefile.toml`
- `lean-toolchain`
- the LeanFpAnalysis library or a dependency path to a clean checkout
- public library docs: `README.md`, `docs/LIBRARY_LOOKUP.md`, examples
- the same task file used in Condition A, copied without edits

Generated Condition C must not contain:

- `.codex/`
- `thesis/DECISION_LOG.md`
- benchmark task-spec notes
- previous attempts or solutions
- any reference proof files

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

Before running an agent attempt, the generated task file should typecheck with
`sorry` allowed.

After an agent attempt:

- run `lake build`;
- reject if any `sorry`, `admit`, new `axiom`, or weakened theorem remains;
- record build result, diff, proof lines, and failure reason.
