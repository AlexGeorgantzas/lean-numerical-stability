# Book-formalization migration gates

This is the executable migration sequence for NumStability.  A gate is complete
only when its stated evidence is checked into the repository or recorded by CI.

The active repository-wide operating contract is
[`phases/2026-08-repository-reorganization-completion/`](phases/2026-08-repository-reorganization-completion/README.md).
Its current C0004 checkpoint freezes the complete 2,766-module inventory,
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
`codex-lane` expired. At C0003, M05/M06 became ready while M07 and every other
unaccepted milestone remained planned and no successor wave was activated.

R05 and R06 have since been preserved by separate true merges, after which
the reviewed 67-path R0006/R0007 union was applied exactly once from their
common C0003 preimages. The bounded integration follow-up ledger remains
exactly 13 unique paths: 6 aggregate paths adding 31 casefold-sorted import
edges over 29 unique destinations, 3 milestone-DAG/evidence paths, and 4
narrative paths. Its zero cross-wave-repair count was the pre-battery
expectation. The later approved R0008 amendment is a separate 27-path
compatibility repair, disjoint from those 13: 4 paths supersede union
postimages through an exact SHA-256 custody chain and 23 are newly staged. The
immutable union manifest is not recut. Variant A keeps the Algorithms umbrella
Source ceiling at 49 and needs no layout exception. R0008 registration covers
16 logical governance paths (5 request artifacts, including the immutable
`R0008-approval.md` addendum, 2 delivered branch records, 3
milestone-DAG/evidence paths, 4 narratives, and 2 validators); because 7 were
already staged, it added 9 unique paths. One stale Algorithms smoke-test
correction brought the exact integration range to 111 paths (78 before R0008
+ 23 repair-only + 9 registration-only + 1 smoke correction). The earlier
battery exposed one stale Source-only Algorithms `#check`; it was removed under
D1 and the targeted smoke file passes. Final candidate evidence run
`.lake/integration-r05-r06-20260816T172806Z` passed all 11 gates with a stable
tree, including the full `NumStability`/`NumStabilityTest` build and `lake test`
(`DONE.json` SHA-256
`A5DA29ED1EE40AF2A4B3967EDB1981ECB041A5821D61EDD117F3F8A55735C166`).
Independent package and committed-diff audits are green.

C0004 accepts M05/R05 and M06/R06 at exact code
`783ae9a4951407ece046adb8631d5a8ff1795a18`; Lean CI run 31962707569 (job
95203051003) passed. P0006/P0007 are retired immutable evidence, and
R0006/R0007/R0008 are applied.
The temporary second-operator authority and R05/R06 reservations are released.
M04/R04 and M08/R08 are ready; every other unaccepted milestone remains
planned and no successor wave is activated. The official baseline, inventory,
and 111-path ledger SHA-256 values are
`D3F30A410903B1CA2858951CB26107B94B62630BC424723A0EC9EDF484AEDDDF`,
`08FA3E41DA0C72E7F5D4ECFD315F0CC6C73EB0F45089CF1DAC6AB04A81A1E326`,
and `E5F12E1834F848C7A2FAAD674BBDEEC0B3760B44BE17D073460E87F3E437F378`.
Bounded-phase and repository-wide completion remain incomplete with 200 debt
rows, including 191 unclassified modules, 125 noncanonical names, and eight
declaration-bearing umbrellas. Acceptance-control commit
`131a0c6f333de0eb47a67698decf36ee82e01dab` passed Lean CI run 31966141900
(job 95211495907); `primary-human` retired B0006/B0007 at
`2026-08-16T19:08:57Z`. Their exact remote refs were deleted atomically under
expected-tip leases and verified absent. The archive root
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0004-R05-R06-20260816`
contains five verified R05 material files totaling 117,327,061 bytes; R06 had
no material artifacts. Named worktrees `completion-r05-claude` and
`completion-r06-codex` were removed without force with no residue. Local
delivery branches remain preserved at
`26e89100b3c7c8a64a41426d517cbd563a40db72` and
`bfaf2ae917ed79165caa6cc58b3782984aa8d3d9`. The
[`R05/R06 retirement review`](phases/2026-08-repository-reorganization-completion/reviews/R05-R06-retirement.md)
records the exact leases, archive, cleanup, and preserved refs.

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
