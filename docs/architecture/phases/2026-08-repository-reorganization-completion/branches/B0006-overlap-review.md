# B0006/R05 overlap review at exact C0003

Fresh exact-C0003 pair review (see `reviews/C0003-R05-R06-selection.md`).
Graph: `benchmark-results/C0003-combined.tsv` SHA-256
`98199873425E068D3B74F8595A6CFB9AFE5532974186FD760DFD122B0D273626`.

R05 vs R06 is zero on all seven dimensions under the R11/R12 standard:
owner exact/ancestor 0/0, destination overlap 0, direct owner imports 0/0,
transitive owner reachability 0/0, typed signature edges 0/0, proof-body
edges 0/0, shared direct outside production consumers 0. The only raw
shared direct importers are the integrator-owned global umbrella
aggregates `NumStability.Algorithms` (both waves), which the R11/R12
precedent classifies as the harmless common umbrella set, handled by the
reviewed R0006/R0007 union.

Every R05 route is a whole-owner route: no owner splits across
destinations, so no private-sharing component can separate (the R03
fanIn7 class of defect is impossible by construction). Retargeted
consumers keep their full transitive surface because each destination
carries its owner verbatim including the owner's complete original import
list; the dot-notation field-projection scan is recorded in
`B0006-field-projection-scan.tsv` (Chapter27.SoftwareEnvironment lesson).

The concurrent wave R06 shares no owner, destination, edge, or
production consumer with R05; both waves' shared requests intersect only
on the integrator-owned control paths and `NumStability/Algorithms.lean`,
resolved by the reviewed union `requests/R0006-R0007-union.patch`.
