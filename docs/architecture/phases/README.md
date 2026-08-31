# Reorganization phases

The active operating contract is the
[`2026-08 repository reorganization completion`](2026-08-repository-reorganization-completion/README.md),
selected by [`active-phase.json`](active-phase.json). It is rooted at C0000 on
accepted predecessor code commit
`b1b18772d80185ec08f49c818919558645c330a1`. The predecessor
[`2026-08 repository reorganization`](2026-08-repository-reorganization/README.md)
phase is formally superseded via its
[`supersession.json`](2026-08-repository-reorganization/supersession.json), and
`tools/architecture/check_phase.py --all-phases` enforces the fleet
invariants, including exactly one effectively active phase and valid acyclic
supersession chains.

The accepted checkpoint is C0008 at exact code commit
`897557779a2102aa0e23b0b2f63edeb35b06bc68`, which accepts milestone M13 with
its I01 wave and is the evidence checkpoint for bounded-phase completion;
repository-wide completion remains incomplete. Its parent C0007 at exact
integrated code commit `4e26820d1f4989ec4ec77b7113085f593570e11b` accepted M09
and M10, moved B0011 and B0012 to accepted with retirement due, retired P0011
and P0012, and applied R0012 and R0013. R0014 and R0015 (the M13 I01 wave plus
the CODE03 correction) are applied on `main` at commit
`9fbb1e36bcc85f866893e902cbe206ba468a65b0` under the primary human's recorded
2026-08-30 cutover decision, which retired the bounded
plan/activate/deliver/integrate lifecycle; the bounded branch
`codex/reorg-closeout-2026-08-m13-i01` remains immutable history at
`46c42a339b59a08cec3cbc439a929c3707447229`, and the operative light-regime
process is recorded in [`docs/architecture/PROCESS.md`](../PROCESS.md). The
live tree records 2,928 of 2,928 production modules classified, with zero
unclassified, mixed, or noncanonical modules and zero declaration-bearing
umbrellas; 712 forwarding modules cover 2,364 canonical targets, and
provenance records 137 Apache-2.0-marked production files and 5 evidenced
upstream modules. Bounded-phase and repository-wide completion both remain
incomplete. The
[`C0007 governance reconciliation review`](2026-08-repository-reorganization-completion/reviews/C0007-governance-reconciliation.md)
records the cutover decision and the reconciled current-state measurements.

This successor has precedence over dated migration packets and historical
handoffs. Closed or superseded phases remain here as immutable evidence. A
retained phase must identify its status and successor rather than silently
changing its original scope.

## Archived chronology

The records below are preserved as past-tense history with their exact
hashes, CI runs, and figures; the normative current-state summary above
supersedes any status language they contain.

Checkpoint C0005 was accepted at exact integrated code commit
`ad92bbfae62d538f3e52829a269a846688a8e213`.
C0005 accepts M04/R04 and M08/R08 on top of C0004's accepted R05/R06. Its
generated evidence records 2,818 production modules: 2,685 classified, 133
unclassified, and 0 mixed. M04 and M08 are accepted; M07 became ready and
B0010/R07 was delivered from exact C0005 base code
`ad92bbfae62d538f3e52829a269a846688a8e213`. Immutable delivery
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

After C0001 acceptance-control commit
`93883eb0ec69a01704ff24ac71713a03f0be5a49` passed Lean CI run 31542177523
(job 93946871439), B0001/B0002 were retired at
`2026-08-11T22:34:24Z`; their exact remote refs were deleted with expected-tip
leases and verified absent. Their ignored evidence is archived under
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0001-R01-R02-20260811`,
and both clean named worker worktrees were removed without force. Local branch
refs remain preserved at the immutable delivery tips.

B0003/R11 (QR and Chapter 19) and B0004/R12 (Chapter 13 equations and Table 01)
were delivered from exact C0001 code
`117aa2bb7e61f41e1531a78452f9f7f6cd5b0771` at immutable tips
`444a03259af510bdfe0921d1847b6add1b26ed73` and
`0726678a0f2db56e533f3b956a2f7f1531059d7d`, respectively. Separate true merge
commits `10169717ce4966e9963885b04e7b7733a3bc7730` and
`1495047a1befb1431f0501cf7a423c8e77f8661a` preserve both deliveries. After
both merges, the reviewed 133-path R0003/R0004 union was applied exactly once
from its common C0001 preimage; sequential whole-file request replacement was
not used. The bounded integration follow-up completes the Chapter 19
`Sensitivity` and `StoredLoop` aggregates and records self-ratcheting
exceptions for exactly the two retained historical imports in byte-identical
`Chapter19.Core`. Exact-code Lean CI run 31673501960 (job 94362951630) passed
for `9d2334d77f1a38f8a4caa81fe53eeb11a8e3e7cd`. At C0002, M11/M12 are
accepted, B0003/B0004 are retired, P0003/P0004 are retired immutable evidence,
and R0003/R0004 are applied. Acceptance-control commit
`c92c48a348a0e09e7d6ac9d4ff1db7673a027648` passed Lean CI run 31678412178
(job 94378054384) before both exact remote refs were deleted with expected-tip
leases. Ignored delivery evidence is hash-verified under
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0002-R11-R12-20260813`,
both clean named worker worktrees were removed without force, and local branch
refs remain preserved at the immutable delivery tips. The temporary
`codex-local` authorization expired at C0002 and `claude-lane` is restored to
its single `claude-local` operator. C0002 recorded 2,642 production modules and
356 distinct residual-debt rows, including 277 unclassified modules, so neither
bounded nor repository-wide completion was claimed. A fresh exact-C0002
singleton review advanced M03/R03 to ready/active controls B0005/P0005/R0005.
Planned-control commit `fb5a021b4640dd595a99f7560ce252ad9836a5b6`
passed Lean CI run 31691727184 (job 94420320315) before B0005 was created
explicitly from exact C0002 code, pushed as a new remote ref with a
nonexistent-tip lease, and activated with its clean LF-configured named
worktree. A reviewed temporary second-operator expansion (`claude-local`,
control `c4f66cbdf`) and a reviewed fanIn7 private-closure route amendment
(control `09b3962dc`) followed, each with green Lean CI. The R03 delivery landed
at immutable tip `1f8ff4ca5` (parent exact C0002), is preserved by true merge,
and the same-C0002 R0005 request was applied exactly once.

C0003 accepts M03/R03 at exact green code commit
`e20de2f931caa12221e708c341e9cb4f64d29b25` (Lean CI run 31799323377). Against
the expected R0005 postimage, 115 request paths are byte-exact and exactly six
contain only their reviewed bounded deviations: two aggregate-sort
reconciliations, tier and compatibility reconciliation, the layout ratchet,
and the `Chapter27.SoftwareEnvironment` consumer import-superset repair. The
complete merge-to-integration audit separately accounts for exactly 21
additional paths: 11 aggregate follow-ups, 3 R03 test paths, 4 narrative
documents, and 3 milestone-DAG/evidence paths. At C0003, P0005 is retired
immutable evidence and R0005 is applied. After exact green control-chain head
`a61438448beb02773ef6b0f4f50cbedf8d675d29` passed Lean CI run 31833811860
(job 94875463331), `primary-human` retired B0005 at
`2026-08-14T19:44:43Z`. Its exact remote delivery ref
`refs/heads/codex/reorg-completion-2026-08-r03-floating-point-foundations-ch01-ch12`
was deleted under an expected-tip lease and verified absent. Seven ignored material artifacts
totaling 117,422,618 bytes were archived and verified at
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0003-R03-20260814`;
the named worktree `C:\Users\qed_s\higham-worktrees\completion-r03-codex` was
removed without force after its `.lake`-only residue was moved recoverably to
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0003-R03-20260814\disposable-worktree-residue\completion-r03-codex`.
The local
delivery branch remains preserved at
`1f8ff4ca5b0b136901a2f47d43e1064dc09aa556`. The
[`R03 retirement review`](2026-08-repository-reorganization-completion/reviews/R03-retirement.md)
records the exact lease, archive, residue, worktree, and local-ref evidence;
the hash-pinned
[`R03 activation review`](2026-08-repository-reorganization-completion/reviews/R03-activation.md)
preserves the earlier authority and activation facts. The temporary
`claude-local` second-operator authority on `codex-lane` expired, restoring
that lane to `codex-local` alone. At C0003, M05 and M06 became ready while
M07/R07 and every other unaccepted milestone remained planned and no successor
wave was activated.

C0003 records 2,690 production modules and 310 distinct residual-debt rows:
254 unclassified, zero mixed, zero missing-module-doc, 217 noncanonical, and 15
declaration-bearing-umbrella rows, with zero unsorted aggregate imports. The
inventory has 2,356 complete rows, 334 in-scope rows, and 310 rows with debt.
Bounded-phase and repository-wide completion remain incomplete.

A fresh exact-C0003 successor review selected the R05+R06 pair — the only
candidate pair zero on all seven overlap dimensions under the R11/R12
standard. B0006/R05 and B0007/R06 were planned from exact C0003 code with
whole-owner routes only, frozen shared requests R0006 (23 paths) and R0007
(49 paths) intersecting on exactly five integrator-owned paths under a
reviewed union, identity projection replays for P0006/P0007, and a reviewed
temporary `claude-local` second-operator expansion scoped to B0006 expiring
at C0004. Planned-control commit `b6794f326313f8077c0c3433bb9c76b6e2ed5361`
passed Lean CI run 31844203563 (job 94907208819) before both worker refs were
pushed with nonexistent-tip leases at exact C0003 code and activated with
clean LF-configured named worktrees. C0003 remained current through activation.

The immutable R05 and R06 deliveries are now preserved by separate true
merges, followed by exactly one application of the reviewed 67-path
R0006/R0007 union from their common C0003 preimages. The bounded integration
ledger remains exactly 13 unique follow-up paths: 6 aggregate paths (31 sorted
edges over 29 unique destinations), 3 milestone-DAG/evidence paths, and 4
narrative paths. Its zero cross-wave-repair count was the pre-battery
expectation. Approved amendment R0008 separately repairs 27 compatibility
paths and is disjoint from those 13: 4 replace union postimages through an
exact SHA-256 chain, 23 are additional integration paths, and the union
postimage manifest remains untouched. The Source-trim decision keeps the
Algorithms umbrella ceiling at 49 without changing the layout baseline.
Registration covers 16
logical governance paths (5 request artifacts, including the immutable
`R0008-approval.md` addendum, 2 delivered branch records, the existing 3
DAG/evidence paths, these 4 narratives, and 2 validators); 7 were already
staged, so 9 were new. One stale Algorithms smoke-test correction brought the
exact integration range to 111 paths (78 before R0008 + 23 repair-only + 9
registration-only + 1 smoke correction). The earlier battery exposed one
stale Source-only Algorithms `#check`; it was removed under D1 and the targeted
smoke file passes. Final candidate evidence run
`.lake/integration-r05-r06-20260816T172806Z` passed all 11 gates
with a stable tree, including the full `NumStability`/`NumStabilityTest` build
and `lake test` (`DONE.json` SHA-256
`A5DA29ED1EE40AF2A4B3967EDB1981ECB041A5821D61EDD117F3F8A55735C166`).
Independent package and committed-diff audits are green.

C0004 accepts M05/R05 and M06/R06 at exact green code commit
`783ae9a4951407ece046adb8631d5a8ff1795a18`; Lean CI run 31962707569 (job
95203051003) passed. P0006/P0007 are retired immutable evidence, and
R0006/R0007/R0008 are applied.
The temporary second-operator authority and R05/R06 reservations are released,
restoring `codex-lane` to `codex-local` alone. M04/R04 and M08/R08 are ready
and their successor branches are activated below; every other unaccepted
milestone remains planned. Acceptance-control commit
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
[`R05/R06 retirement review`](2026-08-repository-reorganization-completion/reviews/R05-R06-retirement.md)
records the exact leases, archive, cleanup, and preserved refs.

Exact-C0004 successor activation recorded
[`B0008/R04`](2026-08-repository-reorganization-completion/branches/B0008.json)
and
[`B0009/R08`](2026-08-repository-reorganization-completion/branches/B0009.json)
as active branches, with frozen baseline projections P0008/P0009 and active
common-base requests R0009/R0010. The 28- and 14-path requests intersect on
exactly five integrator-owned files and are reconciled by the reviewed
[`37-path common-base union`](2026-08-repository-reorganization-completion/requests/R0009-R0010-union-review.md).
The
[`selection review`](2026-08-repository-reorganization-completion/reviews/C0004-R04-R08-selection.md)
records zero peer overlap across every enforced dimension. The
[`temporary operator authorization`](2026-08-repository-reorganization-completion/reviews/R04-R08-operator-authorization.md)
adds `codex-local` to `claude-lane` solely for B0008/R04; B0009/R08 remains
`claude-local`-only. Planned-control commit
`2d9dbf7bf8b4b51e9cb7817f5c5dc2d5194e8c42` passed exact Lean CI run
32030191197 (build job 95388234941). The
[`activation review`](2026-08-repository-reorganization-completion/reviews/R04-R08-activation.md)
pins the two atomic new refs and clean LF-configured named worktrees at exact
C0004. At activation time the 37-path union remained integrator-only and
unapplied, and both workers remained frozen until that activation-control
commit passed its exact Lean CI build job; the deliveries, the integration,
and the C0005 acceptance recorded above all landed afterward.

C0004 records 2,766 production modules and 200 distinct residual-debt rows:
191 unclassified, zero mixed, zero missing-module-doc, 125 noncanonical, and
eight declaration-bearing-umbrella rows, with zero unsorted aggregate imports.
Its inventory has 2,555 complete rows, 211 in-scope rows, and 200 rows with
debt. The C0004 baseline, inventory, and 111-path ledger SHA-256 values remain
pinned at
`D3F30A410903B1CA2858951CB26107B94B62630BC424723A0EC9EDF484AEDDDF`,
`08FA3E41DA0C72E7F5D4ECFD315F0CC6C73EB0F45089CF1DAC6AB04A81A1E326`,
and `E5F12E1834F848C7A2FAAD674BBDEEC0B3760B44BE17D073460E87F3E437F378`;
the accepted C0005 baseline and inventory supersede them.

The planned-control commit `c48d241532ad3dee12f4107a5e8875c7054159be`
passed Lean CI run 31546978830 (job 93961477202) before the R11/R12 refs and
clean named worktrees were created and activated.

[`R11-R12-retirement.md`](2026-08-repository-reorganization-completion/reviews/R11-R12-retirement.md)
records the acceptance CI, exact-lease deletions, archive manifest, clean
worktree removal, and local-ref preservation.

The immutable predecessor
[`2026-08 repository reorganization`](2026-08-repository-reorganization/README.md)
remains the historical record. Its final accepted checkpoint is C0008 at code commit
`b1b18772d80185ec08f49c818919558645c330a1`. M01 through M12 are accepted;
M90 is ready but remains unactivated, and repository-wide completion remains
incomplete. B0011/W07 and B0012/W10 were delivered from exact C0007 at
immutable tips
`176c72838828795b89f4aa822479010c7860c8e5` and
`9e7604cbdbd2314bc4bf38bcd9e342c3accfb1d6`, respectively. Separate true
merge commits preserve both deliveries. C0008 accepts both waves; P0012/P0013
are retired immutable evidence and independently C0007-based R0010/R0011 are
applied. Both branch records are accepted and retired. After C0008
acceptance-control commit `5d047643efbc06e69d380a4266010d9f48d934e1`
passed [Lean CI](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31469704946),
both exact remote refs were deleted atomically with exact expected-SHA leases
at `2026-08-11T07:47:20Z` by `primary-human`. The ignored W07 artifacts were
archived under
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0008-W07-20260811`;
its named delivery worktree was removed without force, and both local branches
remain preserved at their immutable tips. The clean W10 post-delivery
integrator recovery/correction checkout at `C:\Users\qed_s\w10-worker`
remains preserved outside retirement. B0008/W04,
B0009/W09, and B0010/W11 are accepted at C0007 and retired;
P0009/P0010/P0011 are retired and R0007/R0008/R0009 are applied. After the
C0007 acceptance-control commit passed Lean CI, their three exact remote refs
were deleted atomically with exact expected-SHA leases at
`2026-08-08T22:05:06Z` by `primary-human`. W04 never had a local worktree. The
ignored W09/W11 delivery artifacts were archived under
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0007-W09-W11-20260808`;
their named worktrees were removed, and their local branches remain preserved
at the immutable delivery tips.
B0006/W06 and B0007/W08 are accepted at C0006 and retired; their exact remote
refs were deleted at `2026-08-04T13:33:21Z` after the C0006 acceptance-control
commit passed Lean CI, while local branches and worktrees remain preserved.
B0004/W03 and B0005/W05 are
accepted at C0005 and retired; their exact remote delivery refs were deleted
after the C0005 acceptance-control commit passed Lean CI.

Exact-C0006 successor planning recorded
[`B0011/R09`](2026-08-repository-reorganization-completion/branches/B0011.json)
and
[`B0012/R10`](2026-08-repository-reorganization-completion/branches/B0012.json)
as planned branches, with frozen baseline projections P0011/P0012 and active
common-base requests R0012/R0013. The 23- and 7-path requests intersect on
exactly five integrator-owned files and are reconciled by the reviewed
[`25-path common-base union`](2026-08-repository-reorganization-completion/requests/R0012-R0013-union-review.md).
The
[`selection review`](2026-08-repository-reorganization-completion/reviews/C0006-R09-R10-selection.md)
records zero peer overlap across every enforced dimension. B0011/R09 ran in
`claude-lane`; the immutable scope freeze assigned R10 to `codex-lane`, so B0012
ran there under a
[`temporary operator authorization`](2026-08-repository-reorganization-completion/reviews/R10-operator-authorization.md)
adding `claude-local` to that lane. At planning time no worker ref or worktree
existed and neither wave was activated; both waves were subsequently
activated, delivered, and integrated. R09 reclassified the 72
`Higham28*` owners and R10 the last 18 `RandNLA*` owners, which emptied the
unclassified ratchet. Integration control
`09512c1b15fd4f6892a313341b1edc8c02bb913d` preserves both immutable delivery
tips by separate true merges and applies the reviewed 25-path R0012/R0013 union
exactly once.
