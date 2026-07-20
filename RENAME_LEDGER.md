# NumStability Rename and Reorganization Ledger

This ledger records the migration from `lean-fp-analysis` / `LeanFpAnalysis` to
`lean-numerical-stability` / `NumStability`.

## Target identity

| Item | Target |
| --- | --- |
| GitHub repository | `lean-numerical-stability` |
| Lake package | `numStability` |
| Lean library | `NumStability` |
| Root import | `import NumStability` |

## Target source layout

```text
NumStability/
├── FloatingPoint.lean
├── FloatingPoint/
├── Analysis.lean
├── Analysis/
├── Algorithms.lean
└── Algorithms/
```

- `FloatingPoint` contains the arithmetic model and floating-point foundations.
- `Analysis` contains reusable error-analysis and stability theory.
- `Algorithms` contains results about specific numerical algorithms.
- The hierarchy stays shallow. Existing algorithm subdirectories are retained
  where they already group a substantial topic.

## Migration plan

- [x] Record and push the pre-migration tag.
- [x] Create the migration branch.
- [x] Rename the Lake package, Lean library, root module, imports, and namespace.
- [x] Move floating-point foundations to `NumStability/FloatingPoint`.
- [x] Move reusable analysis to `NumStability/Analysis`.
- [x] Move algorithm-specific material to `NumStability/Algorithms`.
- [x] Add the root and category umbrella imports.
- [x] Update documentation, scripts, workflows, and repository-facing metadata.
- [x] Verify no unintended references to the old identity remain.
- [x] Run a complete build and root-import smoke test.
- [ ] Rename the GitHub repository and update the local remote.
- [x] Validate the pushed migration from a clean checkout.
- [ ] Create the first release after the migration reaches `main` under the new identity.

## Decisions

1. Module paths follow the shallow target layout, while declarations retain one
   public namespace, `NumStability`. The previous API also used one shared
   namespace; adding category namespaces would create artificial boundaries and
   needlessly break cross-module references.
2. The old `FP` wrapper is removed because it obscures the distinction between
   foundations, general analysis, and algorithms.
3. No forwarding modules for `LeanFpAnalysis` will be added unless downstream
   users are identified during validation.
4. Existing filenames and meaningful algorithm subdirectories are preserved;
   this migration will not invent a deeper taxonomy.
5. The repository rename happens after the source builds under the new identity.
6. The unused placeholder executable is removed, leaving a library-only package.

## Checkpoints

| Checkpoint | State | Evidence |
| --- | --- | --- |
| Baseline | Passed | `lake build`: 4,429 jobs at `dea467e17` |
| Safeguard tag | Passed | `pre-numstability-rename` pushed to `origin` |
| Migration branch | Passed | `codex/numstability-rename` |
| Identity rename | Passed | Lake package `numStability`; Lean library and root `NumStability` |
| Source reorganization | Passed | 596 Lean modules moved into the three shallow categories |
| Category builds | Passed | `FloatingPoint`: 1,467 jobs; `Analysis`: 3,085 jobs; `Algorithms` covered by the full root build |
| Full validation | Passed | `lake build NumStability`: 4,429 jobs; `lake env lean examples/LibraryLookup.lean` |
| Clean checkout | Passed | Clean clone of `b532d4164`; locked `lake build NumStability`: 4,429 jobs |
| Repository rename | Pending | |

## Migration log

- 2026-07-20: Started from clean `main` at `dea467e17`.
- 2026-07-20: Verified that `pre-numstability-rename` resolves to `dea467e17` and
  pushed the annotated tag to `origin`.
- 2026-07-20: Created branch `codex/numstability-rename`.
- 2026-07-20: Renamed the package, library, root module, imports, and shared
  namespace; reorganized sources under `FloatingPoint`, `Analysis`, and
  `Algorithms`.
- 2026-07-20: Passed the floating-point and analysis category builds.
- 2026-07-20: The forced rebuild of the 113,000-line `HighamChapter9` module
  exposed one pre-existing uncached associativity goal in otherwise unchanged
  proof code. Added the missing `mul_left_comm`; the isolated module then built
  successfully.
- 2026-07-20: The same forced rebuild exposed one pre-existing uncached
  reassociation goal in the 100,000-line `LeastSquares/LSE` module. Added the
  missing `mul_assoc`; the isolated module and its dependents then built.
- 2026-07-20: Passed the complete 4,429-job root build and the curated
  `import NumStability` lookup smoke test.
- 2026-07-20: Cloned the pushed migration branch at `b532d4164` into a clean
  temporary checkout and replayed the locked 4,429-job root build successfully.
