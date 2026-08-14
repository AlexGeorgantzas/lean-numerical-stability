# R03 projection replay — P0005

Run under `Local\lean-reorganization-2026-08` with the checker P0005 pins
(`tools/architecture/check_completion_phase_projection.py`,
SHA-256 `0F32935ED1EFDD2BD4D6A4C346F3E8300C86DB1D4A3551A17165479226109220`), the frozen
projection `9D221D2DF34D79D67799F2F4F3ED16D74365A7EEBBDB372700EF574242F16D53`, and the
complete 398-row private map
`EB2729C65CCAFF1ED4FE6712C3373A78570088D2BCC07FB18DE72B7033721146`, per the delivery
rule recorded in `reviews/R03-projection-replay.md`. The recorded
`--candidate-sha256` pins the unchanged C0002 preimage graph and is therefore dropped
for the delivery replay; the delivery candidate is the fresh worker graph.

```text
phase projection contract passed
candidate_sha256: 98199873425E068D3B74F8595A6CFB9AFE5532974186FD760DFD122B0D273626
selected_declarations: 2389
relocated_declarations: 2132
signature_edges: 28180
body_edges: 42404
candidate_declarations_scanned: 56903
candidate_edges_scanned: 649259
allowed_exact_modules: 47
allowed_prefixes: 48
private_normalizations: 398
```

The comparison is exact set equality on the kind-tagged incident edges after private
normalization, so passing means the frozen C0002 graph and the delivered worker graph
agree edge for edge. 2,132 relocated + 257 retained = 2,389, matching
`DECLARATION_ROUTES.tsv` + `RETENTION.tsv` row for row. The route amendment does not
change the projection: only owning modules moved, and P0005 permits any allowed
module/prefix owner.
