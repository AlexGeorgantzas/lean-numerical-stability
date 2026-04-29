# T01_ScaledDot Smoke Run Summary

- Task: `T01_ScaledDot`
- Run root: `/tmp/lean-fp-benchmark-runs/T01_ScaledDot-20260429-134311`
- Result archive: `benchmark/results/T01_ScaledDot/20260429-134311`
- Shared Lake package cache: used
- Peak archived run workspace size observed: about `101M`

## Outcome

- Condition A: failed validation.
- Condition C: passed validation.

Condition A was manually terminated after about ten minutes because it was still
exploring proof infrastructure and the attempted task still contained `sorry`.
Its `codex_exit_code` is `143` and `validation_exit_code` is `1`.

Condition C completed successfully.  Its `codex_exit_code` is `0` and
`validation_exit_code` is `0`.

## Why This Is A Smoke Run

This run was used to verify that the benchmark harness works end to end without
recloning Mathlib or consuming excessive disk.  It is not an official benchmark
measurement because the solver timeout support was added after Condition A was
manually stopped and before Condition C was run.

The run is still useful as a harness check: it confirms that a fresh isolated
Condition C solver can use the public library to prove the task while the bare
Condition A setting does not solve it in the same controlled attempt.
