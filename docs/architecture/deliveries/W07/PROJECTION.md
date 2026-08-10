# W07 projection result - P0012

W07 compares one final full format-2 candidate with the active P0012
projection using the exact checker argument vector recorded in `P0012.json`.
The replay changes only the candidate placeholder.

## Pinned controls

`CHECK_PROJECTION.py` verifies these artifacts before invoking the official
projection checker:

| Artifact | SHA-256 |
| --- | --- |
| `branches/B0011.json` | `41EFB88CE76180E1C0BBD803A605F560D3B339B3BBC5B132B6003E88A520FFF2` |
| B0011 overlap review | `67E704A1A8CA8FCDA43F20EB428FA0BE1423BAB7EAB4314CC7D5BF9BECEFD500` |
| C0007 checkpoint record | `7D5E6E25CC1FBB96B3BC792DF79E9D39425DE26BFAF3523069BA210D8D3095D3` |
| C0007 inventory | `56B08C666F4461BE2B425E12B2E250ACFCD4604A43F793A066AA086091365196` |
| C0007 integrator-path inventory | `007FECE988156DE622788EA388CF4217FB71B560D6305436F560CA29E83A3C43` |
| C0007 gate evidence | `FD53B43E6D31EBDD2B4A2F62E3324E30747B2AE3E8DAA8D80333DD02B597054F` |
| C0007 combined JSON | `D9372A79DA159CEB50757F6581F650957D2868E738E41C0D5F892C121623CADD` |
| C0007 combined Markdown | `A9C897F4E2EDCDE3B3CAFE5D297B11A05E5D20BA5CC2AF3BD746C90D02F5D3AC` |
| C0007 raw format-2 graph | `80AE3FBB3948104C60FF7EA80E899CC11CE542D0A772EA087375C00EB0ED9ED3` |
| `projections/P0012.json` | `093C8F260B8303E112FE5DF5B3636473021365C2E81C3725B5BE2A3FBD2BB024` |
| `projections/P0012.tsv.gz` | `9B683940DE4C94D17E48E200D1F10594EB26614CFD2AEF2BCB036F667BB5159C` |
| `selectors/W07.tsv` | `478EFA94CE2311ECD54A7AA4A155336EF3DB8219BFA42E137BA7C37D0D97176A` |
| projection checker | `29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443` |
| baseline generator | `AD1B19090B75936C874E6762989E4F06C0C1434C7DC7078E13499570BA3B6A63` |
| Lean declaration extractor | `04AE8E46F66A0B8D2FED1FDB83904D8A60398F9B61A3EC4A10ADB3DF2352D771` |

The wrapper also requires active B0011/P0012 metadata and the exact 42-argument
vector: five owner allowances, 34 destination-prefix allowances, the candidate
placeholder at zero-based index 39, the recorded projection hash, and the
recorded projection path. It neither adds a candidate-hash argument nor changes
any recorded argument other than the placeholder.

## Expected projection

| Quantity | P0012 value |
| --- | ---: |
| Selected declarations | 252 |
| Theorems | 192 |
| Definitions | 48 |
| Inductives / constructors / recursors | 4 / 4 / 4 |
| Public / private declarations | 244 / 8 |
| Signature edge rows | 800 |
| Body/proof edge rows | 1,400 |
| Union edges | 1,474 |
| Relocated / retained | 136 / 116 |

The official checker compares declaration identity, kind, visibility, allowed
owner scope, and exact typed signature and body/proof incident-edge sets. A
successful replay is therefore edge-for-edge preservation, not a count-only
comparison. The wrapper additionally requires the complete candidate scan
totals of 56,903 declarations and 649,259 typed edge rows, preventing a
truncated incident-subgraph candidate from passing.

## Source boundary

The 136 relocated declarations split into 47 reusable and 89 exact Chapter 17
declarations. The 116 retained declarations are the 31-node private graph floor
plus 85 declarations retained solely by classify/document authority. Static
graph checks require zero worker-owned reusable-to-Source and
canonical-to-historical reachability before projection replay.

## Actual candidate and replay

The single final full format-2 candidate completed in 140.331 seconds under the
named Lean mutex. It contains 56,903 declarations in 1,581
declaration-bearing modules, 266,387 signature rows and 382,872 body/proof rows
(649,259 typed rows total), and 424,082 union edges. Its immutable artifacts
are:

| Artifact | SHA-256 |
| --- | --- |
| TSV | `52AA6A6AAF8C2A843B3C78C7D1AC6198381FDDC30DDFCD1BCDC3FFAA8648CF98` |
| JSON | `D556FDDCF4AF07194905E0F87C3D4F0B583FC946CA642D5BF85176CC2D73454D` |
| Markdown | `FB8DD7FE622059B679971878A06B3AFAB8B37D3DCCA1A80470C5C49C92C31558` |

`CHECK_PROJECTION.py` then completed the exact official replay in 4.331
seconds. Its result was:

```text
phase projection contract passed
projection_sha256: 9B683940DE4C94D17E48E200D1F10594EB26614CFD2AEF2BCB036F667BB5159C
candidate_sha256: 52AA6A6AAF8C2A843B3C78C7D1AC6198381FDDC30DDFCD1BCDC3FFAA8648CF98
selected_declarations: 252
relocated_declarations: 136
signature_edges: 800
body_edges: 1400
candidate_declarations_scanned: 56903
candidate_edges_scanned: 649259
allowed_exact_modules: 5
allowed_prefixes: 34
candidate_sha256=52AA6A6AAF8C2A843B3C78C7D1AC6198381FDDC30DDFCD1BCDC3FFAA8648CF98
retained_declarations=116
union_edges=1474
P0012 argument vector preserved: 42 arguments; only candidate placeholder replaced
```

The official checker and W07 wrapper therefore establish exact declaration and
typed-edge preservation with no loss, mismatch, out-of-scope relocation, or
truncated-candidate substitution.
