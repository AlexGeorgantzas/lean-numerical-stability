# Lane baseline projections

Each live branch references one active projection tied to the current accepted
checkpoint's combined format-2 baseline. A projection freezes the exact
historical declarations and every typed incident edge selected for that wave,
together with its checker, allowed owner roots, and expected counts.

The projection records are:

- [`P0001`](P0001.json), retired W01 evidence;
- [`P0002`](P0002.json), retired W02 evidence selected by
  [`W02.tsv`](../selectors/W02.tsv);
- [`P0003`](P0003.json), the superseded C0002 projection for W12; and
- [`P0004`](P0004.json), the retired W12 projection selected by
  [`W12.tsv`](../selectors/W12.tsv);
- [`P0005`](P0005.json), the retired C0004 W03 projection selected by
  [`W03.tsv`](../selectors/W03.tsv); and
- [`P0006`](P0006.json), the retired C0004 W05 projection selected by
  [`W05.tsv`](../selectors/W05.tsv);
- [`P0007`](P0007.json), the retired C0005 W06 projection selected by
  [`W06.tsv`](../selectors/W06.tsv); and
- [`P0008`](P0008.json), the retired C0005 W08 projection selected by
  [`W08.tsv`](../selectors/W08.tsv);
- [`P0009`](P0009.json), the retired C0006 W04 projection selected by
  [`W04.tsv`](../selectors/W04.tsv);
- [`P0010`](P0010.json), the retired C0006 W09 projection selected by
  [`W09.tsv`](../selectors/W09.tsv); and
- [`P0011`](P0011.json), the retired C0006 W11 projection selected by
  [`W11.tsv`](../selectors/W11.tsv);
- [`P0012`](P0012.json), the retired C0007 W07 projection selected by
  [`W07.tsv`](../selectors/W07.tsv); and
- [`P0013`](P0013.json), the retired C0007 W10 projection selected by
  [`W10.tsv`](../selectors/W10.tsv).

P0004 is tied to the C0003 combined baseline generated at code commit
`bb80c95a4625e07535dacdda12d246ee1a5795b3`. Its baseline JSON has SHA-256
`9061CD6CFCA44F838339DE79A5245081951231D2B4F271018C6F460451F370DA`.
The P0004 projection graph is byte-identical to P0003's deterministic gzip
stream and has SHA-256
`892C767A3A72F288283F95B89A06F48B7020C80C61BF9449948C6B4A34F81BFA`.

P0005 and P0006 are independently derived from the hash-verified C0004
combined format-2 graph at code commit
`b56f609f3bf66b5d7d0b677567cce82fee0c275b`. The C0004 baseline JSON has
SHA-256
`CCF7ACAE1D9306C03D79495B548E598C9A3132DC99A98C4212219A453CB27FA8`.
P0005 freezes 1,034 declarations, 8,056 signature edges, 11,608 body/proof
edges, and 11,932 union edges at SHA-256
`7B5A07528409CCCDC8B45F94B8F5FC977A2749601F8ED2D6B18D161CD27838B7`.
P0006 freezes 921 declarations (121 definitions and 800 theorems), 8,562
signature edges, 6,894 body/proof edges, and 11,020 union edges at SHA-256
`6A15BC343C895BCE66A92B09EC333300CA842BEC249DDF2DC723D0832098FFB5`.

P0007 and P0008 are independently derived from the hash-verified C0005 raw
format-2 graph with SHA-256
`1DA19910927D41F4B45266ABA3F5E1A1F165637F7E984F8A19E15DA4FBB4A8D0`.
P0007 freezes 3,512 W06 declarations, 15,044 signature edges, 16,341
body/proof edges, and 22,079 union edges at SHA-256
`E1C2787CC0D0D8A08E016932CEBC1831FAD6929BF22FA757D12BFC49F8ADCF39`.
P0008 freezes 2,179 W08 declarations, 9,266 signature edges, 15,315 body/proof
edges, and 16,573 union edges at SHA-256
`032F33236618FD21D318344A80F8E5EA02F18CCA533C4E183BD61945E6D77D74`.

P0009, P0010, and P0011 are independently derived from the hash-verified C0006
raw graph above. P0009 freezes 1,238 W04 declarations, 5,684 signature edges,
10,044 body/proof edges, and 10,624 union edges at SHA-256
`EAA15F18127E7B77F8AF442760590687B66A8860485590F2EB13D57E3A6F3814`.
P0010 freezes 1,865 W09 declarations, 3,639 signature edges, 7,414 body/proof
edges, and 7,721 union edges at SHA-256
`2F01FAA44AF7984DAA3769512E879DEB4C1EF328130EF24E93E712C9602E1F71`.
P0011 freezes 3,354 W11 declarations, 19,096 signature edges, 26,201 body/proof
edges, and 28,652 union edges at SHA-256
`0A13EF31C40C997E2A692AC595E96DD3416BA603C6EC4ED47AB60765E6EBB3E2`.

P0012 and P0013 are independently derived from the hash-verified C0007 raw
format-2 graph with SHA-256
`80AE3FBB3948104C60FF7EA80E899CC11CE542D0A772EA087375C00EB0ED9ED3`.
P0012 freezes 252 W07 declarations, 800 signature edges, 1,400 body/proof
edges, and 1,474 union edges at deterministic gzip SHA-256
`9B683940DE4C94D17E48E200D1F10594EB26614CFD2AEF2BCB036F667BB5159C`.
P0013 freezes 1,029 W10 declarations, 2,394 signature edges, 4,844 body/proof
edges, and 5,075 union edges at deterministic gzip SHA-256
`B61F64FC0C2CEF8DF22DDA78C5F28BB8D6B64FC1B57392AA36A2E187F3396ABA`.
They are retired immutable evidence for B0011/B0012, accepted at C0008. Both
worker refs were initialized at exact C0007 code SHA
`9eb534a06db267203c2b9b88227edd44fc64f5db` only after planned-control commit
`ac3bc1063c7d9aa1c7a0c12a85337c858b6f9200` passed
[Lean CI](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31300495624).
Active-control commit `cb5fa161bcf6827c7d15e61df9dd9ded34f39327`
subsequently passed Lean CI before work began. Delivery intake alone did not
retire either projection; exact delivery and integrated-candidate replays were
required and passed before C0008 acceptance.

At C0005 the integrator replayed both exact recorded argument vectors against
one full integrated format-2 candidate with SHA-256
`1DA19910927D41F4B45266ABA3F5E1A1F165637F7E984F8A19E15DA4FBB4A8D0`.
P0005 passed with 1,034 selected and 806 relocated declarations, 8,056
signature edges, 11,608 body/proof edges, and 11,932 union edges. P0006 passed
with 921 selected and 783 relocated declarations, 8,562 signature edges,
6,894 body/proof edges, and 11,020 union edges.

At C0006 the integrator replayed P0007 and P0008 against the same full
integrated format-2 candidate with SHA-256
`3BFEFF5663DA3FB5327B9D3AB22806654C9A79A48E1DDFE3C6E2E79073F9DE11`.
P0007 passed with 3,512 selected, 2,737 relocated, and 775 retained
declarations, 15,044 signature edges, 16,341 body/proof edges, and 22,079 union
edges. P0008 passed with 2,179 selected, 1,994 relocated, and 185 retained
declarations, 9,266 signature edges, 15,315 body/proof edges, and 16,573 union
edges.

At C0007 the integrator replayed P0009, P0010, and P0011 against the same full
integrated format-2 candidate with SHA-256
`80AE3FBB3948104C60FF7EA80E899CC11CE542D0A772EA087375C00EB0ED9ED3`.
P0009 passed with 1,238 selected, 1,018 relocated, and 220 retained
declarations, 5,684 signature edges, 10,044 body/proof edges, and 10,624 union
edges. P0010 passed with 1,865 selected, 1,295 relocated, and 570 retained
declarations, 3,639 signature edges, 7,414 body/proof edges, and 7,721 union
edges. P0011 passed with 3,354 selected, 3,129 relocated, and 225 retained
declarations, 19,096 signature edges, 26,201 body/proof edges, and 28,652 union
edges.

At C0008 the integrator replayed P0012 and P0013 against the same full
integrated format-2 candidate with SHA-256
`7973041136A13FEEBACA1C462868A9C9A3DB907FC7D8BC841601E14B3853F1C8`.
P0012 passed with 252 selected, 136 relocated, and 116 retained declarations,
800 signature edges, 1,400 body/proof edges, and 1,474 union edges. P0013
passed with 1,029 selected, 895 relocated, and 134 retained declarations,
2,394 signature edges, 4,844 body/proof edges, and 5,075 union edges.

A worker generates one full format-2 candidate under the shared Lean mutex,
then invokes `tools/architecture/check_phase_projection.py` with every sorted
argument in its projection JSON. The candidate placeholder is replaced by the
candidate TSV path; no other recorded argument is changed.

P0004 refreshed the W12 guard after W02 acceptance; it did not assert that the
two integrations commute. The integrator rewrote W12's 17 direct dependencies
on W02 owners before passing the W12 projection, canonical-import,
strict-source, full-build, and full-test acceptance gates at C0004.

Active projections are replaced whenever their base checkpoint or ownership
contract changes. A terminal branch keeps its retired projection as immutable
evidence; only live branches may reference active projections. P0005 and P0006
are retired with B0004 and B0005 accepted at C0005. P0007 and P0008 are retired
with B0006/W06 and B0007/W08 accepted and retired at C0006. The earlier W03/W05 worker
branches deliberately began at the C0004 code SHA and read later control
records from `origin/main`; activation commits were never copied into a worker
branch. The W06/W08 remote refs likewise began at the exact C0005 code SHA only
after their planned control commit became green and were deleted only after the
C0006 acceptance-control commit became green. P0009, P0010, and P0011 are
retired with B0008/W04, B0009/W09, and B0010/W11 accepted and retired at C0007.
Their exact remote refs were deleted atomically with exact expected-SHA leases
at `2026-08-08T22:05:06Z` by `primary-human` after the C0007 acceptance-control
commit became green. Their worker refs began at the exact C0006 code SHA only after
planned-control commit
`94da2d1e25247d7e9b6661dc188c932cdc6cc1d5` passed Lean CI; the activation
commits remain absent from every worker branch.

P0012 and P0013 are retired with B0011/W07 and B0012/W10 accepted at C0008.
Both deliveries are based on the exact C0007 code SHA and preserved through
separate true merges. The projection records are immutable control evidence on
`main`; they are never copied into worker history. Their exact deterministic
streams were replayed against the same final integrated candidate with only
the candidate-path argument changed. After C0008 acceptance-control commit
`5d047643efbc06e69d380a4266010d9f48d934e1` passed Lean CI, both exact remote
refs were deleted atomically with exact expected-SHA leases at
`2026-08-11T07:47:20Z` by `primary-human`. The ignored W07 artifacts were
archived under
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0008-W07-20260811`;
its named delivery worktree was removed without force, and both local branches
remain preserved at their immutable delivery tips. Projection retirement alone
did not authorize early deletion. The clean post-delivery W10 integrator
recovery/correction checkout
at `C:\Users\qed_s\w10-worker` remains preserved outside worker retirement.
