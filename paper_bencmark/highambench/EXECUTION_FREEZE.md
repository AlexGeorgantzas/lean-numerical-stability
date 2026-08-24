# HighamBench execution freeze

This document defines the handoff from task construction to measured execution
on the `benchmark_exec` branch.

## Repository checkout versus execution package

The Git checkout is a trusted outer-runner input. It is not the filesystem shown
to an evaluated agent. The checkout retains the benchmark sources, execution
tools, NumStability source, and audit provenance. The hash-covered evaluation
package in `metadata/release_files.json` is narrower:

- the common and condition-L prompts;
- all controlled task manifests;
- each task's `Target.lean`, `context.md`, and `task.json`, plus `paper.json`;
- the controlled `shared/HighamBench` sources;
- execution, validation, analysis, and report tools;
- the corpus, run-order, library, package, and live-canary manifests needed by
  the runner.

Task-local `faithfulness/` directories, corpus audit history, reference PDFs,
construction reviews and evidence other than the two required live canaries,
developer notes, `.DS_Store` files, and Python unit tests are outside that
execution package. Their presence in the checkout cannot expose them to an
attempt.

## Files visible inside an attempt

Every run starts from an empty temporary workspace. The runner verifies the
task's controlled manifest and stages only:

- `agent_prompt.md`;
- the core and exact paper-scoped shared Lean source modules;
- that task's `Target.lean` and `context.md`.

Both conditions receive the same read-only paper-scoped compiled bundle at
`/shared-olean`, the same pruned package runtime at `/packages`, and the same
Lean toolchain at `/lean`.

Condition N receives no NumStability source, compiled file, documentation,
index, or cache. Condition L additionally receives these exact read-only mounts:

- `NumStability/` at `/library/NumStability`;
- `NumStability.lean` at `/library/NumStability.lean`;
- the pruned compiled NumStability tree at `/library-olean`.

For this reason the repository checkout must retain `NumStability/` and
`NumStability.lean`. The runner requires those paths below `project_root` and
verifies them against `metadata/library_source.json` and the frozen source
commit before starting any run. The mount distinction, not deletion from Git,
enforces the N/L comparison.

## External frozen artifacts

The branch does not store platform-specific compiled trees or secrets. The
Linux execution host must provide the exact artifacts recorded by the metadata:

- Lean 4.29.0-rc3 toolchain;
- pruned package runtime;
- paper-scoped shared `.olean` bundles;
- pruned NumStability `.olean` tree;
- compiled offline shell launcher and bubblewrap;
- pinned Codex binary and authentication file.

The branch and those external artifacts together form the runnable snapshot.
`run_matrix.py` verifies every recorded hash and exact file set before releasing
a prompt.

## Finalization order

Run these steps only after no Builder or Auditor is changing task or shared
files:

1. Rebuild every paper-scoped shared `.olean` bundle on the frozen Linux host.
   A bundle must contain exactly the compiled counterpart of every shared source
   in that paper's manifest scope.
2. Update `metadata/environment.json` with the exact shared-bundle hashes.
3. Run `tools/task_tags.py` over the complete corpus.
4. Run `tools/refresh_snapshot.py --phase construction` once.
5. Run the full private construction check for all 60 tasks in both N and L and
   promote one exact 120/120 record as `current_final`.
6. Bind the required two fresh final construction reviews to that exact manifest
   hash.
7. Run `tools/refresh_snapshot.py --phase measurement-ready` with the approved
   exact-target novelty override when required by the frozen review policy.
8. Rerun and promote both live canaries after the refresh invalidates their old
   descriptors.
9. Run the complete `run_matrix.py` startup verification on the benchmark host.
   Do not release the first measured prompt until it reports a clean frozen
   environment.
10. Commit the generated metadata as one freeze commit. Any later controlled or
    external-artifact change creates a new snapshot and invalidates all measured
    runs from the earlier snapshot.

The macOS development checkout can run source and unit checks, but it cannot
produce the final environment identity: the frozen execution environment is
Linux x86-64 and requires `/bin/bwrap`, `/usr/bin/python3.10`, and the recorded
external compiled trees.
