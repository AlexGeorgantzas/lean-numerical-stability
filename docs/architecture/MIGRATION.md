# Book-formalization migration gates

This is the executable migration sequence for NumStability.  A gate is complete
only when its stated evidence is checked into the repository or recorded by CI.

The active repository-wide operating contract is
[`phases/2026-08-repository-reorganization-completion/`](phases/2026-08-repository-reorganization-completion/README.md),
operated per [`PROCESS.md`](PROCESS.md). Its current accepted checkpoint is
C0008 (exact code commit `897557779a2102aa0e23b0b2f63edeb35b06bc68`, green on
Lean CI run 33354902730), which accepts milestone M13 with its I01 wave and is
the evidence checkpoint for bounded-phase completion; repository-wide
completion remains incomplete. Its parent C0007 (exact code commit
`4e26820d1f4989ec4ec77b7113085f593570e11b`, green on Lean CI run 32794282084)
accepted M09 and M10, moved B0011 and B0012 to accepted with retirement due,
retired P0011 and P0012, and applied R0012 and R0013 as the reviewed 25-path
union. R0014 and R0015
(the M13 I01 + CODE03 union) have since been applied on `main` at
`9fbb1e36bcc85f866893e902cbe206ba468a65b0` under the primary human's recorded
2026-08-30 cutover decision, which retired the bounded worker lifecycle; after
that landing the live tree records 2,928 production modules: 2,928 classified,
0 unclassified, and 0 mixed, with zero noncanonical names. Branch retirement
remains a separate later control. Bounded-phase and repository-wide completion
both remain incomplete.
The checkpoint distinguishes bounded-phase from repository-wide completion and
records branch, baseline, shared-request, build-lock, and lifecycle rules.
Validate the phase fleet with
`python tools/architecture/check_phase.py --all-phases`, which also enforces
the supersession fleet invariants. Dated packets and
migration reports are evidence, not current worker instructions.

## Archived checkpoint history

C0005 accepted M04/R04 and M08/R08 at exact integrated code commit
`ad92bbfae62d538f3e52829a269a846688a8e213`. Its generated evidence records
2,818 production modules: 2,685 classified, 133 unclassified, and 0 mixed. M04
and M08 were accepted and M07 was ready. B0010/R07 was delivered at
`2f55e0aa5687829ca3a7dd54d5f90663ec4293cc` and its code was integrated on
`main` at `b2b9ab9057deda15c3fcf27745b76dcc49d3a1a5`, after which the live
tree recorded 2,860 production modules: 2,770 classified, 90 unclassified, and
0 mixed. R09 and R10 were then integrated at
`09512c1b15fd4f6892a313341b1edc8c02bb913d`, after which the live tree recorded
2,927 production modules: 2,927 classified, 0 unclassified,
and 0 mixed, with zero noncanonical names. Checkpoint C0006 (exact code commit
`fda296b2079acae3bf1d3565b2dc6e45dc8f6ef5`) is accepted: M07 is accepted,
B0010 is accepted with retirement due, P0010 is retired, and R0011 is
applied.

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
At C0004 time, M04/R04 and M08/R08 were ready and every other unaccepted
milestone remained planned; both were later accepted at C0005 as recorded
above. The C0004 baseline, inventory,
and 111-path ledger SHA-256 values remain pinned at
`D3F30A410903B1CA2858951CB26107B94B62630BC424723A0EC9EDF484AEDDDF`,
`08FA3E41DA0C72E7F5D4ECFD315F0CC6C73EB0F45089CF1DAC6AB04A81A1E326`,
and `E5F12E1834F848C7A2FAAD674BBDEEC0B3760B44BE17D073460E87F3E437F378`;
the accepted C0005 baseline and inventory supersede them. Bounded-phase and
repository-wide completion both remain incomplete; after the R09/R10
integration and the subsequent R0014/R0015 landing, the live tree measures 0
unclassified modules, 0 noncanonical names, and 0 declaration-bearing
umbrellas. Acceptance-control commit
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

## Archived Chapter 14 matrix-inversion compatibility completion (delivered)

R08 was delivered, integrated, and accepted at C0005. It preserved 42
historical Algorithm import paths as declaration-free compatibility
modules, relocated their remaining C0004 declarations whole-owner into 21 new Source
leaves, and converted the Chapter 14 Problem13, Problem14, and Problem15 entry points
into declaration-free aggregates. The accepted W08 regression suite remained unchanged;
the R08 delivery added isolated old-path, canonical, consumer, focused, private-name, and
aggregate-completeness tests under `NumStabilityTest.Reorganization.R08`.

## Migration gate sequence

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
