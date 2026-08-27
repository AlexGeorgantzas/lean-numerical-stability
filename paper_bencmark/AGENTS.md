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
9. A paper extraction invocation writes only its paper-owned paths. It must not
   run corpus-wide `task_tags.py` or `refresh_snapshot.py`, or rewrite a central
   manifest, environment record, run order, release manifest, or snapshot. For
   T4, initialize `t4_workspace.py`, use the versioned read-only schemas and
   templates, and run `t4_metadata.py freeze/check`; its write set is exactly
   the selected paper's `tasks/P0X/T4/task.json`.
10. After all construction, private-proof, review, and validation gates for one
    paper pass, register it with the generic paper finalizer:

    ```text
    python3 paper_bencmark/highambench/tools/finalize_paper.py \
      --benchmark-root paper_bencmark/highambench \
      --paper-id P0X --phase construction
    ```

    The finalizer validates only `P0X`, rebuilds only its trusted bundle, and
    atomically publishes paper-local controlled manifests and a
    content-addressed `metadata/papers/P0X/registration.json` receipt. In
    construction phase that receipt is a truthful draft until
    `check_construction.py --paper-local-evidence --paper-id P0X` authenticates
    the private N/L evidence and refreshes the same paper receipt; T4 also needs
    its paper-local review receipt. No later corpus merge or serialized refresh
    is required.
11. A paper-local task-tag or validation failure must be fixed before its
    registration receipt is published or benchmark measurements are started.
12. Put every custom statement-facing type, model, algorithm, notation, and
    semantic definition needed by paper `P0X` in
    `shared/HighamBench/P0XDefinitions.lean`. Import only the minimal frozen
    upstream `Std` or `Mathlib` modules directly. Never import
    `HighamBench.Core`, `HighamBench.SemanticCore`, or another paper's
    definitions. Similar semantics needed by two papers are duplicated under
    paper-specific names or namespaces rather than promoted to a shared module.
13. Every target for paper `P0X` must import `HighamBench.P0XDefinitions`.
    Do not import another paper's definition module.
14. The complete custom controlled semantic closure for a target consists of
    that target and its own `P0XDefinitions.lean`. Proof-only helpers,
    certificates, tactics used only by proofs, NumStability adapters, other
    paper modules, `Core`, and `SemanticCore` are forbidden from that closure.
15. Each invocation may write only `tasks/P0X/**`,
    `shared/HighamBench/P0XDefinitions.lean`, `metadata/papers/P0X/**`, and
    `P0X`-namespaced private, review, report, temporary, and compiled-bundle
    paths. Other papers, corpus-wide metadata, generic tools, and schemas are
    read-only. Distinct paper IDs may be extracted, reviewed, validated, and
    registered concurrently; the same paper has one writer.
16. Rebuild the trusted compiled bundle for the selected paper under
    `paper_bencmark/scratch_pad/highambench_environment/shared_olean/P0X/`.
    It contains the compiled paper definitions and no custom module from any
    other paper or shared HighamBench core. Record its exact hashes only in the
    paper-local bundle evidence and registration receipt.
17. Before publishing the paper receipt, compile every target for that paper in
    N and L using its paper bundle. Run negative import probes showing that
    `HighamBench.Core`, `HighamBench.SemanticCore`, and every other paper module
    are unavailable. Corpus consumers discover valid receipts by paper ID and
    derive aggregate views at read time without mutating repository metadata.
