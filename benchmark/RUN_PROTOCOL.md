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
- a task file with the theorem statement and `sorry`
- only the bare definitions required to state that theorem

Generated Condition A must not contain:

- `LeanFpAnalysis/`
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
- a task file with the theorem statement and `sorry`

Generated Condition C must not contain:

- `.codex/`
- `thesis/DECISION_LOG.md`
- benchmark task-spec notes
- previous attempts or solutions
- any reference proof files

## Solver-Facing Task Rule

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

