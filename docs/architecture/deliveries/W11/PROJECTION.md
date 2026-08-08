# W11 projection result - P0011

The W11 format-2 candidate was compared with the active `P0011.tsv.gz`
projection using the exact checker vector recorded in `P0011.json`.  The replay
changed only the candidate placeholder and exited 0 in 4.558 seconds.

## Pinned controls

| Artifact | SHA-256 |
| --- | --- |
| `tools/architecture/check_phase_projection.py` | `29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443` |
| `projections/P0011.json` | `12E8250D43D6C543513B4317C235ACEB2E6B524559EE55EE20D19CFC0780E608` |
| `projections/P0011.tsv.gz` | `0A13EF31C40C997E2A692AC595E96DD3416BA603C6EC4ED47AB60765E6EBB3E2` |
| `selectors/W11.tsv` | `24E3BD565946AECFDBAB9D2D21BF1201B86ECD16197F892E1B62A30162D9EE00` |
| C0006 combined JSON | `E9207AA896EAA547E791FB1CECAC7A6B4E6344E8DC8E15D2EF2372FF90570625` |
| C0006 raw format-2 graph | `3BFEFF5663DA3FB5327B9D3AB22806654C9A79A48E1DDFE3C6E2E79073F9DE11` |
| C0006 inventory | `5A8C01FE644CC2DD1190E2DDFEFBAD0EE16D01BD5F7863086E7D2DE5EE307FCC` |
| `B0010.json` | `168B2D667E8A27DDE167B0691F4B31F1DEF2BD4F63CEC3B42E5912856195C206` |
| B0010 overlap review | `68C2A8B62D4DF1DC7F78CA9C3AD04405B6B0D25E74DC05372E6A0D3F697BC2F2` |
| `tools/architecture/generate_baseline.py` | `AD1B19090B75936C874E6762989E4F06C0C1434C7DC7078E13499570BA3B6A63` |
| `tools/architecture/declaration_dependencies.lean` | `04AE8E46F66A0B8D2FED1FDB83904D8A60398F9B61A3EC4A10ADB3DF2352D771` |

`CHECK_PROJECTION.py` verifies every hash above before running the checker.  It
also requires the recorded vector to contain exactly 54 arguments: 18 exact
owner allowances, 33 destination-prefix allowances, and the candidate
placeholder at index 51.  Every argument other than that placeholder remains
byte-for-byte unchanged.

## Expected projection

| Quantity | P0011 value |
| --- | ---: |
| Selected declarations | 3,354 |
| Theorems | 2,469 |
| Definitions | 813 |
| Inductives / constructors / recursors | 24 / 24 / 24 |
| Public / private declarations | 3,351 / 3 |
| Signature edge rows | 19,096 |
| Body/proof edge rows | 26,201 |
| Union edges | 28,652 |

## Full candidate

The final source tree was built and the candidate was generated under
`Local\lean-reorganization-2026-08`.  Candidate generation exited 0 in
128.861 seconds.  The source scan covered 2,279 Lean modules, 3,487,743 lines,
and 73,146,626 bytes, with zero unresolved project imports and zero cyclic
strong components.  The declaration extractor scanned 56,903 declarations,
266,387 signature rows, 382,872 body/proof rows, 649,259 typed rows, and
424,082 union edges.

The candidate metadata records a clean library source tree at source recovery
commit `5af54ee3b8b14f8ae37e032efc373364c2472fd0`, Lean 4.29.0-rc3, and mathlib
revision `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`.

| Candidate artifact | SHA-256 |
| --- | --- |
| `benchmark-results/W11-candidate.tsv` | `D893E204F8488FB8F686E5F3230C9610988106E600E01A6BF69B36C2191856BE` |
| candidate JSON | `72EFD559DA03C7A7FEAAE84424ED70AFEE551CCA16C63402C476E11CB9E069AB` |
| candidate Markdown | `1EDC1641D0E085120F477E8D2FF07DE926DA459C8FE5D5AB765EC42CFE9F07CD` |

## Exact replay

```text
phase projection contract passed
projection_sha256: 0A13EF31C40C997E2A692AC595E96DD3416BA603C6EC4ED47AB60765E6EBB3E2
candidate_sha256: D893E204F8488FB8F686E5F3230C9610988106E600E01A6BF69B36C2191856BE
selected_declarations: 3354
relocated_declarations: 3129
signature_edges: 19096
body_edges: 26201
candidate_declarations_scanned: 56903
candidate_edges_scanned: 649259
allowed_exact_modules: 18
allowed_prefixes: 33
retained_declarations: 225
union_edges: 28652
checker_exit: 0
```

The checker compares declaration identity, kind, visibility, owner scope, and
the exact typed incident-edge sets.  This is therefore an edge-for-edge
preservation result, not a count-only comparison.  The 3,129 relocated
declarations split into 2,322 reusable and 807 source-specific declarations;
the remaining 225 are exactly the private reverse closure.

## Source boundary

The W11 canonical graph has zero reusable-to-`Source` and zero
reusable-to-historical-facade reachability.  The repository-wide strict-source
scan sees 32 paths from four accepted reusable consumers through stale
historical LowRank imports to eight W11 source leaves.  There are zero direct
forbidden edges, zero mixed targets, zero unresolved imports, and zero cycles.
The exact route-preserving consumer retargets are outside B0010 and are listed
in `INTEGRATOR_REQUESTS.md`; an in-memory replay of those retargets reduces the
32 paths to zero.  No projection mismatch or worker-owned source-boundary
failure is waived.
