# Repository reorganization completion (2026-08)

This active successor is rooted at predecessor C0008 code `b1b18772d80185ec08f49c818919558645c330a1` while preserving `docs/architecture/phases/2026-08-repository-reorganization/` as immutable history; the predecessor phase is formally superseded via its [`supersession.json`](../2026-08-repository-reorganization/supersession.json), enforced by `tools/architecture/check_phase.py --all-phases`. C0000 remains the immutable origin.

The accepted checkpoint is C0008 at exact code commit `897557779a2102aa0e23b0b2f63edeb35b06bc68`, which accepts milestone M13 with its I01 wave and is the evidence checkpoint for bounded-phase completion. Its parent C0007 at exact integrated code commit `4e26820d1f4989ec4ec77b7113085f593570e11b` accepted M09 and M10, moved B0011 and B0012 to accepted with retirement due, retired P0011 and P0012, and applied R0012 and R0013. R0014 and R0015 (the M13 I01 wave plus the CODE03 correction) are applied on `main` at commit `9fbb1e36bcc85f866893e902cbe206ba468a65b0` under the primary human's recorded 2026-08-30 cutover decision, which retired the bounded plan/activate/deliver/integrate lifecycle; the bounded branch `codex/reorg-closeout-2026-08-m13-i01` remains immutable history at `46c42a339b59a08cec3cbc439a929c3707447229`, and the operative light-regime process is recorded in [`docs/architecture/PROCESS.md`](../../PROCESS.md). The live tree records 2,928 of 2,928 production modules classified, with zero unclassified, mixed, or noncanonical modules and zero declaration-bearing umbrellas; 712 forwarding modules cover 2,364 canonical targets, and provenance records 137 Apache-2.0-marked production files and 5 evidenced upstream modules. Bounded-phase completion is recorded complete with C0008 as its evidence checkpoint; repository-wide completion remains incomplete with null evidence and is not implied by C0008. [`reviews/C0007-governance-reconciliation.md`](reviews/C0007-governance-reconciliation.md) records the cutover decision and the reconciled current-state measurements, and [`checkpoints/C0008-gates.md`](checkpoints/C0008-gates.md) records the C0008 acceptance evidence.

`MatrixAlgebra.lean` is protected read-only. Shared consumers, global aggregates, manifests, controls, tools, CI, Lake files, root documentation, and `NumStabilityTest.lean` are integrator-owned. Historical owner imports are preserved through import-only wrappers or source aggregates. Repository-wide completion requires zero classification, mixed-tier, naming, documentation, and declaration-bearing-umbrella debt.

## Archived chronology

The records below are preserved as past-tense history with their exact hashes, CI runs, and figures; the normative current-state summary above supersedes any status language they contain.

Checkpoint C0005 was accepted at exact integrated code commit `ad92bbfae62d538f3e52829a269a846688a8e213`. C0005 accepts M04/R04 and M08/R08. Its generated evidence records 2,818
production modules: 2,685 classified, 133 unclassified, and 0 mixed. M04 and
M08 are accepted; M07 became ready and B0010/R07 was delivered from exact C0005
base code `ad92bbfae62d538f3e52829a269a846688a8e213`. Immutable delivery
`2f55e0aa5687829ca3a7dd54d5f90663ec4293cc` is preserved by true merge
`4e298a102c6f914b42581492152ab9eea1cd0edf`, whose first parent is exact
activation-control commit `35cb1a7c5f136f291398dddd99d8012dcf38f967`. The separate
integration-control commit applies exact R0011 and reviewed correction
`DFF0256BCDAB3DA2A3248D85A5A390E345AE5C49D45C6E099E26E315CF03B909`.
The resulting projection is 2,860 production modules: 2,770 classified, 90
unclassified, and 0 mixed, with the residual queue exactly R09=72 and R10=18.
That queue was subsequently emptied: R09 and R10 were integrated at
`09512c1b15fd4f6892a313341b1edc8c02bb913d` under the reviewed 25-path
R0012/R0013 union, and the post-integration ratchet recorded 2,927 production
modules with 0 unclassified and 0 noncanonical names.
Exact integration-control commit `b2b9ab9057deda15c3fcf27745b76dcc49d3a1a5`
passed GitHub Lean CI run 32616508317 (job 97138028649). Checkpoint C0006 is
accepted by `primary-human` at exact code commit
`fda296b2079acae3bf1d3565b2dc6e45dc8f6ef5`: M07 is accepted at C0006, B0010 is
accepted with retirement due, and P0010 is retired and R0011 is applied with
its reviewed supplemental correction.

Checkpoint C0007 is accepted by `primary-human` at exact code commit
`4e26820d1f4989ec4ec77b7113085f593570e11b`, which passed GitHub Lean CI run
32794282084: M09 and M10 are accepted at C0007, B0011 and B0012 are accepted
with retirement due, P0011 and P0012 are retired, and R0012 and R0013 are
applied as the reviewed 25-path union. The eighteen wave-specific shared-path
reservations are released, leaving seven perennial. C0007 is the first
checkpoint with an empty classification queue; M13 and its I01 wave remained
the phase's outstanding wave work until the R0014/R0015 landing recorded in
the current-state summary above. Both remote worker
refs remain preserved at their immutable deliveries. Branch retirement remains a
separate later control.

B0011/R09 and B0012/R10 were activated at exact C0006 base code
`fda296b2079acae3bf1d3565b2dc6e45dc8f6ef5`. Exact planned-control commit
`b12c9c6b829f9cf80a9ad6cf2d0c55f3530cd0d7` passed Lean CI run 32747422537
(job 97496170577). The local and remote
`claude/reorg-completion-2026-08-r09-test-matrices-ch28` and
`claude/reorg-completion-2026-08-r10-randnla-drineas-mahoney` refs and the
clean LF named worktrees `C:\Users\qed_s\higham-worktrees\completion-r09-claude` and
`C:\Users\qed_s\higham-worktrees\completion-r10-claude` pointed to that exact base at
activation. Both workers remained frozen until the separate activation-control
commit passed Lean CI.
Activation was authorized by a reviewed primary-human activation authorization
that is deliberately narrower than the R07 precedent's semantic review and
records what it does not cover. Both waves were subsequently delivered,
integrated at `09512c1b15fd4f6892a313341b1edc8c02bb913d`, and accepted at
C0007 as recorded above.

R01 (`codex-local`) and R02 (`claude-local`) were delivered from exact C0000, preserved by separate true merges, and accepted at C0001 after exact local gates and GitHub Lean CI run 31539572494 passed. M01 and M02 are accepted, P0001/P0002 are retired evidence, and R0001/R0002/R0002T are applied. After acceptance-control commit `93883eb0ec69a01704ff24ac71713a03f0be5a49` passed GitHub Lean CI run 31542177523 (job 93946871439), B0001/B0002 were retired at `2026-08-11T22:34:24Z`; their exact remote delivery refs were deleted with expected-tip leases and verified absent. Ignored delivery evidence was hash-verified under `C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0001-R01-R02-20260811` before both clean named worker worktrees were removed without force. Local delivery branches remain preserved at their immutable tips; [`reviews/R01-R02-retirement.md`](reviews/R01-R02-retirement.md) records the exact archive manifest and cleanup evidence.

C0001 contains 2,631 production modules and 423 distinct residual-debt rows: 277 unclassified, 9 mixed, 72 missing module docs, 244 noncanonical, and 21 declaration-bearing umbrellas, with zero unsorted aggregate imports. A fresh C0001 import/declaration graph identified R11 (QR/Chapter 19) and R12 (Chapter 13 equations/table) as the only ready pair with zero owner, destination, import, reachability, signature, body, and shared-consumer overlap. Planned-control commit `c48d241532ad3dee12f4107a5e8875c7054159be` passed Lean CI run 31546978830 (job 93961477202); B0003/B0004 were then created from exact C0001 code `117aa2bb7e61f41e1531a78452f9f7f6cd5b0771` and activated synchronously. Both waves retain their immutable `claude-lane` assignment. A primary-human review temporarily authorized `codex-local` only for B0004/R12 through C0002; that authorization is now expired. [`reviews/R11-R12-activation.md`](reviews/R11-R12-activation.md) records the exact refs, worktrees, operators, activation tips, and green planned-control gate.

R11 delivery `444a03259af510bdfe0921d1847b6add1b26ed73` and R12 delivery `0726678a0f2db56e533f3b956a2f7f1531059d7d` are direct children of exact C0001 and are preserved on `main` by separate true merge commits `10169717ce4966e9963885b04e7b7733a3bc7730` and `1495047a1befb1431f0501cf7a423c8e77f8661a`. After both merges, the integrator applied the hash-pinned 133-path reviewed R0003/R0004 union exactly once from the common C0001 preimage; sequential whole-file request replacement was not used. The bounded follow-up completes `NumStability.Source.Higham.Chapter19.Sensitivity` and `NumStability.Source.Higham.Chapter19.StoredLoop` as descendant-complete aggregates and records two exact, self-ratcheting compatibility-import exceptions for the byte-identical retained `NumStability.Source.Higham.Chapter19.Core` outlier.

C0002 accepts R11/R12 after the `architecture`, `canonical_import`, `compatibility`, `focused_build`, `full_build`, `full_tests`, `layout`, `old_import`, `provenance`, `scope`, and `strict_source` gates passed and exact-code GitHub Lean CI run 31673501960 (job 94362951630) completed successfully. M11/M12 are accepted; P0003/P0004 are retired immutable evidence; and R0003/R0004 are applied. Acceptance-control commit `c92c48a348a0e09e7d6ac9d4ff1db7673a027648` passed GitHub Lean CI run 31678412178 (job 94378054384); B0003/B0004 were then retired at `2026-08-13T07:46:11Z`. Their exact remote delivery refs were deleted with expected-tip leases and verified absent. Ignored delivery evidence was hash-verified under `C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0002-R11-R12-20260813` before both clean named worker worktrees were removed without force. Local delivery branches remain preserved at their immutable tips; [`reviews/R11-R12-retirement.md`](reviews/R11-R12-retirement.md) records the exact archive manifest and cleanup evidence. The temporary `codex-local` authority has expired and `claude-lane` is restored to the single `claude-local` operator.

C0002 contains 2,642 production modules and 356 distinct residual-debt rows: 277 unclassified, 9 mixed, 13 missing module docs, 241 noncanonical, and 16 declaration-bearing umbrellas, with zero unsorted aggregate imports. The bounded successor and repository-wide completion therefore remained incomplete. A fresh exact-C0002 review selected M03/R03 alone. Planned-control commit `fb5a021b4640dd595a99f7560ce252ad9836a5b6` passed Lean CI run 31691727184 (job 94420320315); B0005 was then created explicitly from accepted C0002 code `9d2334d77f1a38f8a4caa81fe53eeb11a8e3e7cd`, pushed as a new exact remote ref with a nonexistent-tip lease, and activated with its clean LF-configured named worktree. A reviewed primary-human expansion (`reviews/R03-operator-authorization.md`, control commit `c4f66cbdfdce6cf64d484be13290e7d2e60547f5`, Lean CI run 31719287142) temporarily authorized `claude-local` as the codex-lane second operator solely for B0005/R03, and a reviewed route amendment (`reviews/R03-route-amendment.md`, control commit `09b3962dc6ed18b6de6eea5dc4a0e0e7c8ba4bb7`, Lean CI run 31732612464) repaired the fanIn7 private-closure defect by landing the indivisible three-declaration component whole at the Equation 18 destination, with the Equation 15 module delivered as a documented declaration-free bridge. The R03 delivery — 47 owners, 2,389 declarations (2,132 relocated, 257 retained), 398 private normalizations, 36 documented wrappers, and 2,150 isolated tests, with the exact P0005 delivery replay green under the complete private map — landed at immutable tip `1f8ff4ca5b0b136901a2f47d43e1064dc09aa556` (parent exact C0002) and is preserved by true merge.

C0003 accepts M03/R03 at exact green code commit `e20de2f931caa12221e708c341e9cb4f64d29b25` (Lean CI run 31799323377). The reviewed same-C0002 R0005 request was applied exactly once after the merge: 115 request paths are byte-exact against its expected postimage, and exactly six contain only their reviewed bounded deviations—two aggregate-sort reconciliations, the two genuinely Source-dependent destination reclassifications with matching `reusable_entrypoints` removals, compatibility-row reconciliation, the layout ratchet, and the `Chapter27.SoftwareEnvironment` import-superset repair restoring the pre-existing non-owner `Chapter02.FloatingPointArithmetic.Environment` supply. The complete merge-to-integration audit separately accounts for exactly 21 additional paths: 11 aggregate follow-ups, 3 R03 test paths, 4 narrative documents, and 3 milestone-DAG/evidence paths. At C0003, P0005 is retired immutable evidence and R0005 is applied. After exact green control-chain head `a61438448beb02773ef6b0f4f50cbedf8d675d29` passed Lean CI run 31833811860 (job 94875463331), `primary-human` retired B0005 at `2026-08-14T19:44:43Z`. The exact remote ref `refs/heads/codex/reorg-completion-2026-08-r03-floating-point-foundations-ch01-ch12` was deleted under an expected-tip lease and verified absent. Seven ignored material artifacts totaling 117,422,618 bytes were archived and verified at `C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0003-R03-20260814`; the named worktree `C:\Users\qed_s\higham-worktrees\completion-r03-codex` was removed without force after its `.lake`-only residue was moved recoverably under `C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0003-R03-20260814\disposable-worktree-residue\completion-r03-codex`. The local delivery branch remains preserved at `1f8ff4ca5b0b136901a2f47d43e1064dc09aa556`. [`reviews/R03-retirement.md`](reviews/R03-retirement.md) records the exact lease, archive, residue, worktree, and local-ref evidence; [`reviews/R03-activation.md`](reviews/R03-activation.md) continues to hash-pin the earlier activation facts. The temporary `claude-local` second-operator authority on `codex-lane` expired, restoring the lane to `codex-local` alone. At C0003, M05 and M06 became ready because R03 removed all 9 mixed rows and all 13 missing-module-doc rows and M11 was accepted. M07/R07 and every other unaccepted milestone remained planned, R07 was not activated, and no successor wave was activated.

C0003 contains 2,690 production modules and 310 distinct residual-debt rows: 254 unclassified, zero mixed, zero missing module docs, 217 noncanonical, and 15 declaration-bearing umbrellas, with zero unsorted aggregate imports. Its 2,436 classified modules are 90.558% of production (1,088 source, 377 aggregate, 420 compatibility, 544 reusable, 2 internal, and 5 upstream); 420 wrappers reach 1,171 direct targets under 2 import exceptions. The tracked inventory has 2,356 complete rows, 334 in-scope rows, and 310 debt rows. The tree contains 3,985,082 physical and 1,454,099 nonblank Lean source lines (74,663,808 bytes), 28,305 direct imports (17,193 internal and 11,112 external), and 56,903 elaborated declarations with 266,387 signature, 382,872 body-or-proof, and 424,082 union edges. The bounded successor and repository-wide completion remain incomplete.

A fresh exact-C0003 successor review ([`reviews/C0003-R05-R06-selection.md`](reviews/C0003-R05-R06-selection.md)) selected the R05+R06 pair — the only candidate pair that was zero on all seven overlap dimensions under the accepted R11/R12 standard (R05×R07 and R06×R07 each had a transitive owner-reachability crossing, and R06×R07 had two genuine shared Chapter 28 consumers). B0006/R05 (48 owners, projection P0006, request R0006, 23 paths) and B0007/R06 (75 owners, projection P0007, request R0007, 49 paths) were planned from exact C0003 code `e20de2f931caa12221e708c341e9cb4f64d29b25`. Every route in both waves is a whole-owner route, so the R03 fanIn7 private-closure defect class is impossible by construction, and each destination carries its owner verbatim so retargeted consumers keep their full transitive surface (the Chapter27 lesson; dot-notation field-projection scans are frozen per branch). The requests intersect on exactly five integrator-owned paths resolved by the reviewed [`R0006/R0007 union`](requests/R0006-R0007-union-review.md). Both freeze-time projection replays passed as identity replays ([`reviews/R05-R06-projection-replay.md`](reviews/R05-R06-projection-replay.md)). Planned-control commit `b6794f326313f8077c0c3433bb9c76b6e2ed5361` passed Lean CI run 31844203563 (job 94907208819); both worker refs were then pushed with nonexistent-tip leases at exact C0003 code and activated with clean LF-configured named worktrees (`completion-r05-claude`, `completion-r06-codex`); [`reviews/R05-R06-activation.md`](reviews/R05-R06-activation.md) records the exact refs, worktrees, operators, and tips. The frozen scope kept both waves on `codex-lane`; a reviewed temporary expansion ([`reviews/R05-R06-operator-authorization.md`](reviews/R05-R06-operator-authorization.md)) authorized `claude-local` as second codex-lane operator solely for B0006/R05 through C0004.

C0004 accepted integration: immutable deliveries R05
`26e89100b3c7c8a64a41426d517cbd563a40db72` and R06
`bfaf2ae917ed79165caa6cc58b3782984aa8d3d9`, both parented directly by
C0003, are preserved by separate true merges
`538c7d248a0ccaec407a082ecb73b92d7c3faec2` and
`deee8e7ea0aeac7cfbd9fc2582eaf1f5b841fd0c`. The hash-pinned 67-path
zero-context union patch `requests/R0006-R0007-union.patch` (SHA-256
`639DA03437C3FBAA6934E71B55EFE7D85DF51835D94978790C59162585690D4E`)
was applied exactly once from the common C0003 preimages, never by sequential
whole-file replacement. The bounded follow-up ledger remains exactly 13
unique paths: 6 aggregate paths adding 31 casefold-sorted direct-import edges
over 29 unique destinations, 3 milestone-DAG/evidence paths, and 4 narrative
paths. Its zero cross-wave-repair count was the pre-battery expectation.

The primary-human-approved R0008 integration amendment is a separate 27-path
compatibility repair, disjoint from those 13 paths. It rewrites 26 production
importers plus `docs/architecture/COMPATIBILITY.md`, replacing 59 historical
facade imports and correcting 36 stale compatibility rows; 4 paths replace union
postimages through the exact chain `union postimage_sha256 == R0008
preimage_sha256`, and 23 add integration paths. The immutable
`R0006-R0007-union-postimages.tsv` is not modified. D1 uses the Source-trim
variant, keeping the `NumStability.Algorithms` `NumStability.Source.` ceiling
at 49 without amending `layout-exceptions.json`; D2-D4 are approved, and D3's
facade-to-facade exemption is intentional. R0008 registration covers 16
logical governance paths: 5 request artifacts, including the immutable
`R0008-approval.md` addendum, 2 delivered branch records, 3
milestone-DAG/evidence paths, 4 narratives, and 2 validators. Seven were
already staged in the earlier 13-path ledger, so registration added 9 new paths.
One stale Algorithms smoke-test correction brought the exact integration range
to 111 paths (78 before R0008 + 23 repair-only + 9 registration-only + 1 smoke
correction). The earlier battery exposed one stale Source-only Algorithms
`#check`; it was removed under D1 and the targeted smoke file passes. Final
candidate evidence run `.lake/integration-r05-r06-20260816T172806Z` passed all 11
gates with a stable tree, including the full
`NumStability`/`NumStabilityTest` build and `lake test` (`DONE.json` SHA-256
`A5DA29ED1EE40AF2A4B3967EDB1981ECB041A5821D61EDD117F3F8A55735C166`).
Independent package and committed-diff audits are green.

C0004 accepts M05/R05 and M06/R06 at exact green code commit
`783ae9a4951407ece046adb8631d5a8ff1795a18`; Lean CI run 31962707569 (job
95203051003) passed. P0006/P0007 are retired immutable evidence, and
R0006/R0007/R0008 are applied.
The temporary second-operator authority and all R05/R06 temporary path
reservations are released, restoring `codex-lane` to `codex-local` alone.
M04/R04 and M08/R08 are ready; every other unaccepted milestone remains
planned; the R04/R08 successor branches are activated below.
Acceptance-control commit
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
[`R05/R06 retirement review`](reviews/R05-R06-retirement.md) records the exact
leases, archive, cleanup, and preserved refs.

Exact-C0004 successor activation recorded [`B0008/R04`](branches/B0008.json)
and [`B0009/R08`](branches/B0009.json) as active branches, with frozen
baseline projections [`P0008`](projections/P0008.json) and
[`P0009`](projections/P0009.json) and active common-base shared requests
[`R0009`](requests/R0009.json) and [`R0010`](requests/R0010.json). R04 selects
19 owners and 289 declarations into 31 production destinations; R08 selects 45
owners and 211 declarations into 21 production destinations. The requests
contain 28 and 14 paths, intersect on exactly five integrator-owned files, and
are reconciled by the reviewed
[`37-path common-base union`](requests/R0009-R0010-union-review.md). The
[`selection review`](reviews/C0004-R04-R08-selection.md) records zero peer
overlap across all enforced dimensions. The
[`temporary operator authorization`](reviews/R04-R08-operator-authorization.md)
adds `codex-local` to `claude-lane` solely for B0008/R04; B0009/R08 remains
`claude-local`-only. Planned-control commit
`2d9dbf7bf8b4b51e9cb7817f5c5dc2d5194e8c42` passed exact Lean CI run
32030191197 (build job 95388234941). The
[`activation review`](reviews/R04-R08-activation.md) pins the two atomic new
refs and clean LF-configured named worktrees at exact C0004. At activation
time the 37-path union remained integrator-only and unapplied, and both
workers remained frozen until that activation-control commit passed its exact
Lean CI build job; the deliveries, the integration, and the C0005 acceptance
recorded above all landed afterward.

C0004 contains 2,766 production modules and 200 distinct residual-debt rows:
191 unclassified, zero mixed, zero missing module docs, 125 noncanonical, and
eight declaration-bearing umbrellas, with zero unsorted aggregate imports. Its
2,575 classified modules are 93.095% of production (1,124 source, 377
aggregate, 523 compatibility, 544 reusable, 2 internal, and 5 upstream); 523
wrappers reach 1,425 direct targets under 2 import exceptions. The tracked
inventory has 2,555 complete rows, 211 in-scope rows, and 200 debt rows. The
tree contains 3,986,088 physical and 1,454,947 nonblank Lean source lines
(74,712,781 bytes), 28,456 direct imports (17,344 internal and 11,112
external), and 56,903 elaborated declarations with 266,387 signature, 382,872
body-or-proof, and 424,082 union edges. The official baseline, inventory, and
111-path ledger SHA-256 values are
`D3F30A410903B1CA2858951CB26107B94B62630BC424723A0EC9EDF484AEDDDF`,
`08FA3E41DA0C72E7F5D4ECFD315F0CC6C73EB0F45089CF1DAC6AB04A81A1E326`,
and `E5F12E1834F848C7A2FAAD674BBDEEC0B3760B44BE17D073460E87F3E437F378`.
Bounded-phase and repository-wide completion remain incomplete.
