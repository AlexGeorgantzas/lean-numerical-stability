You are solving a Lean 4 benchmark task in this generated workspace.

Work only inside the current workspace. Prove the theorem in
`BenchmarkTask.lean` by replacing the `sorry` proof with a complete Lean proof.

This is a persistence benchmark. Do not stop after one failed proof idea. Keep
working until `lake build BenchmarkTask` succeeds or the external timeout stops
the attempt.

Persistence requirements:
- Do not leave the original `sorry`.
- Removing `sorry` is not enough. A proof attempt only counts when
  `lake build BenchmarkTask` succeeds.
- If there are no `sorry`s but Lean still reports errors or unsolved goals,
  continue editing until those errors are resolved.
- Do not end with a final message saying the proof is incomplete while there is
  still time to try alternatives.
- If `lake build BenchmarkTask` fails, read the Lean errors, revise the proof,
  and run `lake build BenchmarkTask` again.
- If a theorem name is unavailable, search the files visible in this workspace
  for alternatives, then try another proof route.
- Prefer a small complete proof over a large speculative proof. If one route
  becomes stuck, replace it with a different route rather than stopping.
- Only finish when the proof validates locally with `lake build BenchmarkTask`,
  or when the external timeout terminates the run.

Rules:
- Treat the current workspace as the whole benchmark environment.
- You may inspect files and symlinks that are already present as entries in
  the current workspace, such as `public_library`, `README.md`, `docs`, or
  `examples` when they exist.
- Do not inspect the original repository, user home directories, global caches,
  previous result directories, or manually discovered paths outside the
  workspace.
- Do not add manual `LEAN_PATH`, `--root`, or other search paths. Use the
  imports and Lake package configuration already present in the workspace.
- Only edit the proof body of the theorem in `BenchmarkTask.lean`.
- Do not change imports, task-local definitions, namespaces, or the theorem
  statement.
- Put any helper reasoning inside the theorem proof.
- Do not add `axiom`, `opaque`, `unsafe`, `admit`, or `sorry`.
- After every proof attempt, run `lake build BenchmarkTask` and use the errors
  to continue.
