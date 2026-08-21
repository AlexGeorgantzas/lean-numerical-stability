# HighamBench Builder workflow

## Active rebuild cycle

`Target.lean`, `context.md`, `task.json`, `paper.json`, the paper-specific Lean
definitions, and `TASK_SOURCE_TAGS.md` are the authoritative construction files
while tasks are being repaired. A rebuilt task may be committed and sent for an
independent faithfulness audit before the corpus-wide hash snapshot is refreshed.

For every task, the Builder must still:

- verify the PDF identity used by the source audit;
- check the reconstructed proposition against the paper;
- compile the target and affected definitions;
- compile private N and L proofs and a nonvacuity witness;
- check paper-module isolation; and
- run `tools/task_tags.py`.

During an active multi-task rebuild cycle, do not update these files merely to
propagate hashes:

```text
metadata/controlled/*.json
metadata/manifest.json
metadata/config.json
metadata/environment.json
metadata/release_files.json
metadata/run_order.json
```

Their values may be stale until the next snapshot checkpoint. Do not run
benchmark measurements or claim that the corpus snapshot verifies while this is
the case. The faithfulness audit remains usable because it reads the current
task-local files, imports, and PDF and computes its own audit hashes.

## Snapshot checkpoint

Run one coordinated snapshot finalization only after the rebuild/audit cycle is
stable and no other agent is writing task or audit files:

1. Reconcile the central manifest's semantic entries with the authoritative
   `paper.json` and `task.json` records.
2. Rebuild the affected paper-scoped compiled bundles.
3. Run `task_tags.py` over the complete corpus.
4. Run `refresh_snapshot.py --phase construction` once.
5. Verify every controlled manifest, the release manifest, and the environment
   identity against the settled tree.
6. Commit the generated snapshot metadata together in a dedicated commit.

Use `--phase measurement-ready` only after all repairs, independent audits,
tier decisions, construction proofs, and reviews are complete.

## Deferred simplification

Before measurement, review the current metadata design:

- make `paper.json` and `task.json` the sole semantic authorities;
- make the large central manifest fully generated or replace it with a minimal
  corpus index; and
- reduce the release manifest to runtime inputs and controlled-manifest roots,
  excluding task-local `faithfulness/` history unless it is intentionally part
  of the evaluation package.
