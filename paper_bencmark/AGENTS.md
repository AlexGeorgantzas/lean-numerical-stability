# HighamBench paper-task instructions

These instructions apply whenever any paper entry below
`paper_bencmark/highambench/tasks/` is created, reviewed, or edited. P01, P02,
and every later P0X entry follow the same rules.

1. Read `TASK_SOURCE_TAGS.md` before selecting tasks.
2. Every `task.json` must contain a nonempty `source_tags` list and an
   `author_label` field.
3. The only source tags are `THM`, `LEM`, `PROP`, `COR`, `EQN`, `TXT`, and
   `UNL`.
4. Use `THM`, `LEM`, `PROP`, or `COR` only when the selected result is
   explicitly given that label by the paper. Copy the exact label into
   `author_label`.
5. When the selected result has no explicit named label, set `author_label` to
   `null` and classify its presentation as `EQN`, `TXT`, or `UNL`.
6. Tag the selected task result itself. Do not add tags merely because a
   supporting result cited in its proof has another label.
7. During benchmark construction, keep `classification_frozen_before_runs`
   false. Tags and other task metadata may be corrected at this stage without
   changing the selected result or Lean statement.
8. Assign and review tags before creating a measurement-ready snapshot. The
   same rule applies to existing and newly added paper entries.
9. After adding or editing tasks, run:

   ```text
   python3 paper_bencmark/highambench/tools/task_tags.py \
     --benchmark-root paper_bencmark/highambench
   ```

10. During an active multi-task rebuild cycle, defer corpus-wide hash
    propagation until a stable checkpoint. Do not hand-maintain controlled
    manifests, environment hashes, release hashes, or run-order entries for
    each task. Once no other writer is changing task files, refresh the
    construction snapshot once with:

    ```text
    python3 paper_bencmark/highambench/tools/refresh_snapshot.py \
      --benchmark-root paper_bencmark/highambench --phase construction
    ```

    Until that checkpoint completes, global snapshot metadata may be stale and
    benchmark measurements are forbidden. Use `--phase measurement-ready` only
    when the complete corpus is ready for measured runs.
11. A task-tag validation failure must be fixed before metadata is refreshed or
    benchmark measurements are started.
12. Keep only definitions used by at least two papers in
    `shared/HighamBench/Core.lean`. Put every paper-specific model, algorithm,
    and helper definition in `shared/HighamBench/P0XDefinitions.lean` or, when
    the module must be split for compilation, another `P0X`-scoped module.
    Every paper-scoped import must remain inside that paper's manifest scope.
13. Every target for paper `P0X` must import `HighamBench.P0XDefinitions`.
    Do not import another paper's definition module.
14. Add each shared source to `metadata/manifest.json` under
    `controlled_shared_files` with its exact `paper_ids` scope. The snapshot
    refresh tool derives each target's `shared_files` and controlled manifest
    from that scope. A staged task must contain the core and all of its own
    paper-scoped files, but no file scoped only to another paper.
15. Compile affected definitions and N/L proofs during each task repair. At the
    stable snapshot checkpoint, rebuild the trusted compiled bundle for every
    affected paper under
    `paper_bencmark/scratch_pad/highambench_environment/shared_olean/P0X/`.
    Each bundle must contain compiled objects for exactly the source modules in
    that paper's manifest scope. Record those exact hashes in
    `metadata/environment.json` under `lean.shared_olean_bundles`, then refresh
    the construction snapshot once.
16. Before treating the split as checked, compile every affected target in N
    and L using its paper bundle and run a negative import probe showing that
    the other paper modules are unavailable.
