# R02 projection replay (P0002)

P0002 freezes 142 declarations, 460 signature edges and 945 body/proof edges across the 28
residual owners. All counts were reproduced from the frozen graph before any file was
written, and the 123-member private reverse closure was recomputed and found identical to
B0002's reviewed sheet rather than trusted.

## Result — PASSED

```
phase projection contract passed
projection_sha256:            283E6773D06E2CBE591115BC1EEE388735CDC55BB1D2F4280917078D014EE5BE
candidate_sha256:             308C48787CE3FBF69360841F2487570FB4B721939079CE90D939E8EAD75873CF
selected_declarations:        142
relocated_declarations:       142
signature_edges:              460
body_edges:                   945
allowed_exact_modules:        28
allowed_prefixes:             11
private_map_sha256:           F4E9853B58DA54FBBB1D00340983F796D510DDED3A1ACA79409A62F2D11B66CC
private_normalizations:       76
exit 0
```

Every declaration relocates; nothing is retained. All 76 private normalizations validated
against the pinned private map.

## Pinned artifacts, hash-verified before the replay

| artifact | SHA-256 |
| --- | --- |
| `projections/P0002.tsv.gz` | `283E6773D06E2CBE591115BC1EEE388735CDC55BB1D2F4280917078D014EE5BE` |
| `selectors/R02.tsv` | `FE6BAD5F307EB44A12D410A977118ACF389002F243B68B2A0575139C3BB35069` |
| `baselines/C0000-combined.json` | `2EA9D8C24D3E4D3EEA6B3A135FE195946BB8659C7E5FBF9452DADD89D1726A2F` |
| `tools/architecture/check_completion_phase_projection.py` | `0F32935ED1EFDD2BD4D6A4C346F3E8300C86DB1D4A3551A17165479226109220` |
| `branches/B0002-private-normalization.tsv` | `F4E9853B58DA54FBBB1D00340983F796D510DDED3A1ACA79409A62F2D11B66CC` |

## Argument vector

P0002 records **44** checker arguments. Exactly one substitution was made — the candidate
placeholder — and the other 43 were passed verbatim, as the projections README requires.

## One correction worth recording

The completion phase pins its **own** checker, `check_completion_phase_projection.py`, not
the `check_phase_projection.py` used by the predecessor phase. That file does not exist in
the C0000 worker checkout because it shipped with the phase itself, so a first replay
attempt failed with `FileNotFoundError` — a harness fault, not a projection mismatch. The
replay now exports the checker, and every path-bearing recorded argument, read-only from the
green `origin/main` active-control commit and hash-verifies each against P0002's record
before running.
