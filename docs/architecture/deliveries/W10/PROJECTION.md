# W10 projection replay (P0013)

P0013 freezes 1,029 declarations, 2,394 signature edges, 4,844 body/proof edges and
5,075 union edges across 17,260 physical owner-source lines.

## Pinned control artifacts

| artifact | SHA-256 |
| --- | --- |
| `projections/P0013.tsv.gz` | `B61F64FC0C2CEF8DF22DDA78C5F28BB8D6B64FC1B57392AA36A2E187F3396ABA` |
| raw format-2 projection | `56B8FFD7024AE943C7E35AF3ACCC3106EFCEA068ED68C6AB7B42D0055DE479B0` |
| `selectors/W10.tsv` | `444AA9109E4990AD47E281D550EA7A80057A8DBC493D8AF1693760EE7434BBB0` |
| `baselines/C0007-combined.json` | `D9372A79DA159CEB50757F6581F650957D2868E738E41C0D5F892C121623CADD` |
| `checkpoints/C0007-inventory.tsv` | `56B08C666F4461BE2B425E12B2E250ACFCD4604A43F793A066AA086091365196` |
| `check_phase_projection.py` | `29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443` |

These artifacts and active B0012/P0013 exist in the authoritative control worktree. The
worker auditor takes that checkout explicitly with `--control-root`; it does not claim that
post-C0007 control records are present in the C0007-based worker tree.

## Exact replay

P0013 records 73 arguments: 27 exact owner modules, 43 destination prefixes, the candidate
placeholder, the projection hash, and the projection path. `CHECK_PROJECTION.py` verifies
the pinned artifacts and active records, substitutes exactly the candidate placeholder, and
passes the remaining 72 arguments byte-for-byte to the official checker.

Expected result:

- selected declarations: 1,029;
- relocated declarations: 895;
- signature edges: 2,394;
- body/proof edges: 4,844;
- union edges: 5,075;
- retained declarations: 134 (132 private reverse-closure members plus 2
  separately reviewed full-graph re-entry hazards);
- allow modules/prefixes: 27/43.

The full candidate is also the authority used by `CHECK_STATIC.py` to map every selected
declaration to its actual physical module, closing the earlier coarse-route evidence defect.

## Final full candidate

The final worker candidate is generated with:

`python -B tools/architecture/generate_baseline.py --output-dir benchmark-results --name W10-candidate --keep-dependency-tsv benchmark-results/W10-candidate.tsv`

| artifact | SHA-256 |
| --- | --- |
| `benchmark-results/W10-candidate.tsv` | `749CC6B1888CF99BA5A44AC74A55A51A1DC23FD2EC7BE11D533F0E34BE128E61` |
| `benchmark-results/W10-candidate.json` | `86422CC6BFB76B0D3FF7CF0515232E4DAEB8487473964B628C5252F757C03653` |
| `benchmark-results/W10-candidate.md` | `74EC53E847199D2012E1BC344F8BD7E0118AE6B5065EA35BB7F5D6531C63C9E3` |

The full scan contains exactly **56,903 declarations** and **649,259 typed edges**.
`CHECK_PROJECTION.py` pins the byte size and SHA-256 of all three candidate artifacts,
verifies the decompressed raw P0013 payload, and requires both scan totals in the official
checker output, so a reduced or stale candidate cannot satisfy the delivery evidence.
