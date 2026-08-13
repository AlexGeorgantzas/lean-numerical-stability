# R03 exact-C0002 projection replay

Authority: `primary-human`

P0005 is the complete incident-edge projection of the exact C0002 format-2
graph for the 47 owners in `selectors/R03.tsv`. The worker base is the
accepted C0002 code commit `9d2334d77f1a38f8a4caa81fe53eeb11a8e3e7cd`, never the later retirement or
planning-control commit.

- C0002 raw graph: `benchmark-results/C0002-combined.tsv`
- raw graph SHA-256: `E03DB7A24886AD0B45C7371FE30ACE3AD135B3C4CC9866D65186753CD14FAD4C`
- selector SHA-256: `176BC214ABAE4B9CC2E9822E3177033213C4BD730D0057FBE8BAB524412C6B3A`
- projection gzip SHA-256: `9D221D2DF34D79D67799F2F4F3ED16D74365A7EEBBDB372700EF574242F16D53`
- uncompressed projection payload SHA-256: `7AAB876C821A25ABAD19346BCE35188CF28D1A31C20AF0C931CA1B3AC9892733`
- checker SHA-256: `0F32935ED1EFDD2BD4D6A4C346F3E8300C86DB1D4A3551A17165479226109220`
- private-normalization SHA-256: `EB2729C65CCAFF1ED4FE6712C3373A78570088D2BCC07FB18DE72B7033721146`
- exact checker vector tokens: declarations `2389`; signature edges `28180`;
  body/proof edges `42404`; union edges `43943`; private reverse closure `2502`

Replay on a clean checkout of exact C0002. Acquire the named mutex
`Local\lean-reorganization-2026-08`, generate a fresh format-2 candidate,
verify the raw graph hash above, project every declaration owned by the exact
selector plus every incident typed edge, sort declaration rows by name and
edge rows by `(source, signature-before-body, target)`, and encode with gzip
level 9, empty filename, and `mtime=0`. The resulting bytes must match P0005.

For unchanged-C0002 preimage replay, run the checker vector recorded in
`P0005.json` without the two private-map arguments because private names still
encode their old owners. For worker delivery replay, run the complete recorded
vector including the total 398-row private map. The checker must report no
name, kind, visibility, signature-edge, body-edge, or unauthorized-owner drift.
