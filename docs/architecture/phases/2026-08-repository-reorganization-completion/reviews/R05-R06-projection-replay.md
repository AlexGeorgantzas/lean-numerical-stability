# P0006/P0007 freeze-time projection replay at exact C0003

Both frozen format-2 projections were replayed with
`tools/architecture/check_phase_projection.py` against the exact-C0003
candidate graph `benchmark-results/C0003-combined.tsv` (SHA-256
`98199873425E068D3B74F8595A6CFB9AFE5532974186FD760DFD122B0D273626`)
immediately after generation. Both passed as identity replays
(`relocated_declarations: 0`; every owner still owns its declarations at
freeze time).

| Projection | SHA-256 (`.tsv.gz`) | Selected | Signature edges | Body edges | Allowed exact modules |
| --- | --- | ---: | ---: | ---: | ---: |
| P0006 (R05) | `9F46AC69A6B12D6A21EB5FAEE23D913E4E446C212906CA13CB9AB991E09E589C` | 3,171 | 29,704 | 38,184 | 76 |
| P0007 (R06) | `0549B8A8FAF0196514C2054A5F0B144A8C11C30E0B825447AE5C384150F4E441` | 9,415 | 81,048 | 88,795 | 123 |

Candidate scan: 56,903 declarations, 649,259 edges in both replays.
Union-edge counts: P0006 42,013; P0007 103,659.

The allow lists are exactly each wave's owners plus its frozen whole-owner
destinations (76 = 48 + 28; 123 = 75 + 48), so the delivery replay may move
a declaration only from its owner to that owner's single frozen
destination. Replays at delivery must use these same vectors with the
delivered tree's regenerated candidate and must drop the freeze-time
`--candidate-sha256` pin, which pins this C0003 preimage graph (R03
delivery-replay precedent).
