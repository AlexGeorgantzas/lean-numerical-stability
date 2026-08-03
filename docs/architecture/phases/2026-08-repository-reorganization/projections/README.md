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
  [`W12.tsv`](../selectors/W12.tsv).

P0004 is tied to the C0003 combined baseline generated at code commit
`bb80c95a4625e07535dacdda12d246ee1a5795b3`. Its baseline JSON has SHA-256
`9061CD6CFCA44F838339DE79A5245081951231D2B4F271018C6F460451F370DA`.
The P0004 projection graph is byte-identical to P0003's deterministic gzip
stream and has SHA-256
`892C767A3A72F288283F95B89A06F48B7020C80C61BF9449948C6B4A34F81BFA`.

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
evidence; only live branches may reference active projections. No projection
is currently active; a future branch must create a new projection from C0004.
