# T01_ScaledDot Benchmark Run Summary

- Task: `T01_ScaledDot`
- Run root: `/tmp/lean-fp-benchmark-runs/T01_ScaledDot-20260501-140133`
- Result archive: `benchmark/results/T01_ScaledDot/20260501-140133`
- Timeout: `600` seconds per condition
- Condition C snapshot: `/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/condition-c-snapshots/leanprover-lean4-v4.29.0-rc3-47bb3357162aa7bb`
- Shared Lake package cache: used

## Outcome

- Condition A: failed validation.
- Condition C: passed validation.

Condition A exited normally but did not produce an accepted Lean proof.
Its `codex_exit_code` is `0` and `validation_exit_code` is `1`.

Condition C completed successfully.  Its `codex_exit_code` is `0` and
`validation_exit_code` is `0`.

## Notes

Both conditions used fresh generated workspaces.  Condition A used only the
task-specific stub module.  Condition C used the shared read-only public
library snapshot plus public documentation links.
