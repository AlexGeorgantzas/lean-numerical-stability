# R05 projection replay — P0006

Run under `Local\lean-reorganization-2026-08` with the checker P0006 pins
(`tools/architecture/check_completion_phase_projection.py`), the frozen
projection `9F46AC69A6B12D6A21EB5FAEE23D913E4E446C212906CA13CB9AB991E09E589C`,
and the complete amended 106-row private map
`2FE2A25FD3E8718A871D5F11BCA277C7865A17183420BB344F451D8E792D5A76`
(`reviews/R05-R06-private-map-amendment.md`), per the delivery rule recorded
in `reviews/R05-R06-projection-replay.md`. The freeze-time
`--candidate-sha256` pins the unchanged C0003 preimage graph and is
therefore dropped for the delivery replay; the delivery candidate is the
fresh worker graph.

| measure | value |
| --- | ---: |
| selected declarations | 3,171 |
| relocated declarations | 574 |
| signature edges preserved | 29,704 |
| body edges preserved | 38,184 |
| private normalizations applied | 106 (61 renames + 45 identity) |
| allowed exact modules | 76 (48 owners + 28 frozen destinations) |
| result | `phase projection contract passed` |

Every relocated declaration moved from its owner to exactly that owner's
single frozen destination; declaration names, kinds, visibility, and the
complete typed incident edge sets are preserved.
