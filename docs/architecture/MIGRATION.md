# Book-formalization migration gates

This is the executable migration sequence for NumStability.  A gate is complete
only when its stated evidence is checked into the repository or recorded by CI.

The active repository-wide operating contract is
[`phases/2026-08-repository-reorganization-completion/`](phases/2026-08-repository-reorganization-completion/README.md).
Its current C0003 checkpoint freezes the complete 2,690-module inventory,
assigns every current debt row to a lane and dependency wave, distinguishes
bounded-phase from repository-wide completion, and records branch, baseline,
shared-request, build-lock, and checkpoint lifecycle rules. Validate it with
`python tools/architecture/check_phase.py`. Dated packets and migration reports
are evidence, not current worker instructions.

C0003 accepts M03/R03 at exact code commit
`e20de2f931caa12221e708c341e9cb4f64d29b25`, but it does not claim bounded or
repository-wide completion: 310 distinct residual-debt rows remain, including
254 unclassified modules. The R03 delivery landed at immutable tip
`1f8ff4ca5b0b136901a2f47d43e1064dc09aa556` with parent exact C0002, is
preserved by true merge, and the reviewed same-C0002 R0005 request was applied
exactly once. Its expected-postimage comparison has 115 byte-exact request
paths and exactly six reviewed bounded request-path deviations; a separate 21
paths contain only the documented integration follow-ups. P0005 is retired and
R0005 is applied. After exact green control-chain head
`a61438448beb02773ef6b0f4f50cbedf8d675d29` passed Lean CI run 31833811860
(job 94875463331), `primary-human` retired B0005 at
`2026-08-14T19:44:43Z`. The exact remote delivery ref
`refs/heads/codex/reorg-completion-2026-08-r03-floating-point-foundations-ch01-ch12`
was deleted under an expected-tip lease and verified absent. Seven ignored material artifacts
totaling 117,422,618 bytes were archived and verified at
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0003-R03-20260814`;
the named worktree `C:\Users\qed_s\higham-worktrees\completion-r03-codex` was
removed without force after its `.lake`-only residue was moved recoverably to
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0003-R03-20260814\disposable-worktree-residue\completion-r03-codex`.
The local
delivery branch remains at `1f8ff4ca5b0b136901a2f47d43e1064dc09aa556`.
The [`R03 retirement review`](phases/2026-08-repository-reorganization-completion/reviews/R03-retirement.md)
records the exact cleanup evidence. The temporary `claude-local` authority on
`codex-lane` has expired. M05/M06 are ready; M07 and every other unaccepted
milestone remain planned, and no successor wave is activated.

1. **Current baseline.** Regenerate and version the architecture and build
   report at the exact migration commit using tracked tooling.
2. **Safety net.** Track CI, a test target, API/import smoke tests, and clean and
   incremental benchmark tooling.
3. **Architecture contract.** Define API tiers, dependency directions,
   placement rules, and compatibility policy in `ARCHITECTURE.md`.
4. **Explicit entry points.** Add `Core`, `Higham`, and `All` without changing
   the historical meaning of `import NumStability`.
5. **Separate graphs.** Generate module-import, declaration-signature, and
   proof-body graphs; compute candidate communities and validate them against
   mathematical subject boundaries.
6. **Endpoint pilot.** Review the report's seven all-leaf modules, plus any
   additional endpoints exposed by the corrected declaration extractor;
   classify them without treating endpoint status as deletion evidence.
7. **Performance pilot.** Profile `NonrandomRounding`; change it only when the
   measured elaboration, tactic, or import bottleneck supports a specific fix.
8. **Reusable-family pilot.** Reorganize a contained family such as summation
   with precise imports, compatibility modules, tests, and modern visibility
   where the dependency-closed family permits it. Retain legacy `import`
   syntax when introducing `module` / `public import` would force a repository-
   wide module-system migration.
9. **Semantic source extraction.** Move book-specific aliases, corrections,
   capstones, discrepancies, and cross-chapter glue by meaning and provenance.
10. **Outlier refactoring.** Address the measured compilation queue using
    semantic seams, rebuild fanout, and stable interfaces rather than size alone.
11. **Physical-target decision.** Create a separate source library only if the
    evidence gates in `ARCHITECTURE.md` justify it; otherwise record the decision.
12. **Compatibility release.** Remove forwarding paths only in a planned
    breaking release, then rerun every baseline, build, test, lint, and API gate.

The migration is incremental.  Do not combine mass file moves, declaration
renames, visibility changes, and compatibility removal in one change.
