# R01 P0001 projection replay

P0001 freezes the complete typed graph induced by the 16 R01 owners:

| quantity | frozen count |
| --- | ---: |
| declarations | 243 |
| signature edges | 693 |
| body/proof edges | 1,341 |
| union edges | 1,422 |

## Pinned active-control artifacts

| artifact | SHA-256 |
| --- | --- |
| selector `R01.tsv` | `6D839B9008474CD9CBECEF5EE35FE347B91FD50541F8E347AA8648FF55EF81EB` |
| compressed projection `P0001.tsv.gz` | `DB8ACB22219D5C0C51E3F8F8D5296170FDF92C8C1166C0FDB2598EF6E11728D2` |
| projection checker | `0F32935ED1EFDD2BD4D6A4C346F3E8300C86DB1D4A3551A17165479226109220` |
| C0000 combined baseline | `2EA9D8C24D3E4D3EEA6B3A135FE195946BB8659C7E5FBF9452DADD89D1726A2F` |
| C0000 inventory | `05C2DFB3F1A99F928E90DB3E3EA0C2277320DD3985C476ACB1D529762410776F` |
| B0001 overlap review | `CD1DB2CFC926A545D83D62E378CF38FF442E80D3A2560E2FE60A5082B40DBE7F` |
| declaration routes | `1493383A571EFFDECCD2DF5D5C8DF2657139B2BA140D271B0706C86D32397A52` |
| module routes | `5BAF7963A4806F1A04931C25980C531BEE21B791255C76854E26BEF4149FE0FD` |
| private normalization | `0063E4B0E9C1DAD56F0CCD0A5B9D3897D6F18BEF860482AEB609B83DF6CD4F4A` |

`CHECK_PROJECTION.py` requires the clean active-control checkout at
`daf5c92355e26c07ab0d219c20cd6ce6782b98f3`, re-hashes every pinned artifact,
loads the exact argument vector from active `P0001.json`, and changes only
`--candidate=<candidate-format2.tsv>` to the absolute final candidate path.

## Final ignored format-2 candidate

The candidate was generated under `Local\lean-reorganization-2026-08` after the final
Lean/test edit:

```text
python -B tools/architecture/generate_baseline.py --output-dir benchmark-results --name R01-candidate --keep-dependency-tsv benchmark-results/R01-candidate.tsv
```

Generation exited 0 in 143.257 seconds. The format-2 summary records 56,903
declarations, 266,387 signature edges, 382,872 body/proof edges, 649,259 typed edge
rows, and 424,082 union edges.

| artifact | bytes | SHA-256 |
| --- | ---: | --- |
| `benchmark-results/R01-candidate.tsv` | 116,692,639 | `D2A80F17356569426B23D8B0563D209F4B9D59EC2ACC32A37CD640B4410B8735` |
| `benchmark-results/R01-candidate.json` | 101,759 | `0A552B738B2F0BF88F52818685A519B420627DD4C78B5B2E46317A5FEEF71E73` |
| `benchmark-results/R01-candidate.md` | 19,131 | `6C2FE69D6B6B182FBF9F956E7F27347C038EFC50568041D0961A2FEA437B1519` |

All three artifacts are ignored and untracked. A deterministic summary-only replay with
`--dependency-tsv benchmark-results/R01-candidate.tsv` exited 0 in 23.257 seconds and
reproduced all three hashes byte-for-byte.

## Exact P0001 replay result

The final replay command ran under the same mutex and exited 0 in 4.782 seconds:

```text
python -B docs/architecture/deliveries/R01/CHECK_PROJECTION.py benchmark-results/R01-candidate.tsv --control-root C:\Users\qed_s\higham-worktrees\final-main-audit
```

`CHECK_PROJECTION.py` verified the clean active-control commit, every pinned authority
hash, all 24 recorded arguments with only the candidate placeholder substituted, 16 exact
allowed modules, three allowed prefixes, 243 selected and relocated declarations, 693
signature edges, 1,341 body/proof edges, 1,422 union edges, and all ten approved private
normalizations. Its official checker output also scanned exactly 56,903 declarations and
649,259 typed candidate rows.
