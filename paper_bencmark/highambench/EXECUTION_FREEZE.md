# HighamBench execution freeze

This document defines the final handoff from the fixed task corpus to measured
execution on `benchmark_exec`.

## Repository boundary

The branch contains the task packages and trusted execution tooling. It does
not contain the NumStability source tree. The root Lake package pins and checks
out the library at:

```text
.lake/packages/numStability
4ec1ec874353010ad93cc0bb76370ac321da4681
```

The runner requires this exact Git checkout. It verifies
`metadata/library_source.json` against the package's `NumStability/` tree and
`NumStability.lean`, together with the curated lookup index and its checked Lean
example, before any attempt starts.

The hash-covered evaluation package in `metadata/release_files.json` contains:

- common and condition-L prompts;
- controlled task manifests;
- each task's target, context, and trusted metadata;
- paper-scoped shared Lean sources;
- execution, validation, and analysis tools;
- corpus, run-order, package, library, and live-canary manifests.

Reference PDFs, private proofs, faithfulness artifacts, review records,
construction notes, generated results, Python tests, and the NumStability
development tree are outside the branch and outside every attempt.

## Attempt boundary

Every attempt receives the same Lean toolchain, pruned non-NumStability package
runtime, paper-scoped shared source and `.olean` bundle, fixed target, context,
and common prompt.

Condition N receives no NumStability artifact. Although Lake installs
NumStability as a dependency of the trusted outer checkout, the runtime
projection explicitly excludes the `numStability` package and verifies its
absence before releasing the prompt.

Condition L additionally receives:

- `.lake/packages/numStability/NumStability` mounted read-only at
  `/library/NumStability`;
- `.lake/packages/numStability/NumStability.lean` mounted read-only at
  `/library/NumStability.lean`;
- `.lake/packages/numStability/docs/LIBRARY_LOOKUP.md` mounted read-only at
  `/library/docs/LIBRARY_LOOKUP.md`;
- `.lake/packages/numStability/examples/LibraryLookup.lean` mounted read-only at
  `/library/examples/LibraryLookup.lean`;
- the exact compiled library projection mounted read-only at `/library-olean`.

## External artifacts

Platform-specific files and secrets are never committed. The Linux execution
host must provide:

- Lean 4.29.0-rc3;
- the exact Lake package checkouts from `lake-manifest.json`;
- the pruned non-NumStability package runtime;
- paper-scoped shared `.olean` bundles;
- the compiled NumStability projection;
- bubblewrap and the compiled no-socket shell launcher;
- the pinned Codex binary and authentication file.

## Finalization order

Run these steps on the frozen Linux host after the branch contents stop
changing:

1. Run `lake update` and verify that NumStability and Mathlib resolve to the
   commits recorded in `lake-manifest.json`.
2. Build the frozen NumStability package and create the exact compiled library
   projection used by condition L.
3. Create the pruned package runtime while excluding the `numStability`
   package; confirm that the condition-N import and marker probes fail closed.
4. Rebuild every paper-scoped shared `.olean` bundle from the committed shared
   sources.
5. Regenerate `metadata/library_olean.json`, `metadata/packages_olean.json`,
   `metadata/packages_runtime.json`, and the shared-bundle hashes in
   `metadata/environment.json`.
6. Run `tools/task_tags.py` and the complete private N/L construction check for
   all 60 tasks. Keep private proofs and generated workspaces outside Git.
7. Run `tools/refresh_snapshot.py --phase measurement-ready` to regenerate
   controlled manifests, run order, release hashes, counts, and environment
   identity.
8. Rerun and explicitly promote both live canaries with
   `tools/run_ultra_orchestration_canary.py`,
   `tools/run_token_control_canary.py`, and `tools/promote_live_canary.py`.
9. Run the complete `tools/run_matrix.py` startup verification without
   releasing a measured prompt until every frozen check passes.
10. Commit the generated metadata as one final freeze commit. Any subsequent
    controlled-file, package, binary, or host change creates a new snapshot and
    invalidates measurements made under the earlier identity.

The macOS checkout can validate source manifests and Python structure, but it
cannot create the final environment identity. That identity records the Linux
host, `/bin/bwrap`, Python 3.10 executable, compiled trees, and production
Codex binary.
