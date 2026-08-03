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
  [`W05.tsv`](../selectors/W05.tsv).

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

At C0005 the integrator replayed both exact recorded argument vectors against
one full integrated format-2 candidate with SHA-256
`1DA19910927D41F4B45266ABA3F5E1A1F165637F7E984F8A19E15DA4FBB4A8D0`.
P0005 passed with 1,034 selected and 806 relocated declarations, 8,056
signature edges, 11,608 body/proof edges, and 11,932 union edges. P0006 passed
with 921 selected and 783 relocated declarations, 8,562 signature edges,
6,894 body/proof edges, and 11,020 union edges.

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
are retired with B0004 and B0005 accepted at C0005. No phase projection is
currently active. The worker branches deliberately began at the C0004 code SHA
and read later control records from `origin/main`; activation commits were
never copied into a worker branch.
