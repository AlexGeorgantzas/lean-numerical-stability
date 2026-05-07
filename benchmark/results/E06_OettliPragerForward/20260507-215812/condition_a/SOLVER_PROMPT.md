You are solving a Lean 4 benchmark task in this generated workspace.

Work only inside the current workspace. Prove the theorem in
`BenchmarkTask.lean` by replacing the `sorry` proof with a complete Lean proof.

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
- After editing, run `lake build BenchmarkTask`.
