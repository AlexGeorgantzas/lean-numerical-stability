# Lane baseline projections

Each live branch references one active projection tied to the current accepted
checkpoint's combined format-2 baseline. A projection freezes the exact
historical declarations and every typed incident edge selected for that wave,
together with its checker, allowed owner roots, and expected counts.

P0001 is retained as retired W01 evidence. The active projections are:

- [`P0002`](P0002.json) for W02, selected by [`W02.tsv`](../selectors/W02.tsv);
- [`P0003`](P0003.json) for W12, selected by [`W12.tsv`](../selectors/W12.tsv).

Both use the C0002 combined baseline and deterministic gzip streams. A worker
generates one full format-2 candidate under the shared Lean mutex, then invokes
`tools/architecture/check_phase_projection.py` with every sorted argument in
its projection JSON. The candidate placeholder is replaced by the candidate
TSV path; no other recorded argument is changed.

P0002 and P0003 are independent baseline guards, not evidence that integration
is commutative. W02 is accepted first. W12 is refreshed after that checkpoint,
and the integrator rewrites its 17 direct dependencies on W02 owners before the
W12 projection, canonical-import, strict-source, full-build, and full-test
acceptance gates.

Active projections are replaced whenever their base checkpoint or ownership
contract changes. A terminal branch keeps its retired projection as immutable
evidence; only live branches may reference active projections.
