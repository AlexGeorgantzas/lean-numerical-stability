# R06 projection replay — P0007

The delivery replay used the fresh format-2 worker graph under
`Local\lean-reorganization-2026-08` with the frozen P0007 projection and the
complete amended B0007 private-normalization map. The replay deliberately
drops the freeze-time `--candidate-sha256`, which pins the C0003 preimage; no
candidate hash argument was passed to the delivery checker.

## Pinned inputs

| input | SHA-256 |
| --- | --- |
| `P0007.tsv.gz` | `0549B8A8FAF0196514C2054A5F0B144A8C11C30E0B825447AE5C384150F4E441` |
| `P0007.json` | `C1FEC4C494CB7CE908E49DEC0FA378B5852D897EFA1A35A17A17B22855D19567` |
| projection checker | `0F32935ED1EFDD2BD4D6A4C346F3E8300C86DB1D4A3551A17165479226109220` |
| amended B0007 private map | `A258D47A26D03C8CB9B40F9291BFE8E137820B33956077FEB218ECD0B98B9451` |
| fresh R06 candidate | `06E993418A5FEBD7CE88EE1DAE71C2E0BA9639B8F37B958ABBF0EBCAB155DDC9` |

The P0007 JSON contributes exactly 123 distinct `--allow-module` arguments
(75 owners plus 48 destinations), all exact modules and no prefixes. The
private map is total over P0007 and contains 200 rows: 195 genuine relocation
renames and 5 retained identities.

## Fresh candidate

The candidate is 117,080,989 bytes with one format-2 header. It contains
56,903 declarations: 55,219 public, 1,680 private, and 4 internal. Its 649,259
edge rows comprise 266,387 signature edges and 382,872 body edges (424,082
distinct union edges). The four internal declarations are part of the global
candidate inventory; they do not alter P0007's frozen selected population.

## Replay result

| measure | value |
| --- | ---: |
| selected declarations | 9,415 (9,215 public / 200 private) |
| relocated declarations | 2,094 |
| signature edges preserved | 81,048 |
| body edges preserved | 88,795 |
| private normalizations applied | 200 (195 renames + 5 identities) |
| allowed exact modules | 123 |
| allowed prefixes | 0 |
| result | `phase projection contract passed` |

Every relocated declaration moved from its frozen owner to exactly its frozen
destination. Declaration names, kinds, visibility, and complete typed incident
edge sets are preserved. An independent second replay obtained the identical
candidate hash and counts.
