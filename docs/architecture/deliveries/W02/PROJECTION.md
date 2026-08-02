# W02 projection result — P0002

The locked candidate was compared with `P0002.tsv.gz` using the checker and
projection graph at the exact hashes recorded by `P0002.json`:

| Artifact | SHA-256 |
| --- | --- |
| `tools/architecture/check_phase_projection.py` | `29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443` |
| `P0002.tsv.gz` | `EA781015CD00CDC9EC152D71BE9D6F2993148294E8B3EBEF28B56E81C9C002DB` |
| locked W02 candidate TSV | `16CD7D4421007F75E479F92F34C461ACA0D89BFE41BC121089BC02C69A9E40F2` |

The full candidate build required by locked extraction completed successfully with
5,121 jobs. The comparison used all 73 exact historical modules and all 65 allowed
destination prefixes recorded by the active B0002/P0002 contract.

```text
phase projection contract passed
checker_sha256: 29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443
projection_sha256: EA781015CD00CDC9EC152D71BE9D6F2993148294E8B3EBEF28B56E81C9C002DB
candidate_sha256: 16CD7D4421007F75E479F92F34C461ACA0D89BFE41BC121089BC02C69A9E40F2
selected_declarations: 4195
relocated_declarations: 2220
signature_edges: 18256
body_edges: 30343
candidate_declarations_scanned: 56903
candidate_edges_scanned: 649259
allowed_exact_modules: 73
allowed_prefixes: 65
```

## Deterministic graph replay

A no-build extraction replay reproduced all three locked candidate artifacts:

| Artifact | Replayed SHA-256 |
| --- | --- |
| candidate TSV | `16CD7D4421007F75E479F92F34C461ACA0D89BFE41BC121089BC02C69A9E40F2` |
| candidate JSON summary | `A289FCB92C31076822E62BDF60505857696905C9E7B919A0745CC1514446EF34` |
| candidate Markdown summary | `21BE549665C478735411F2CB30507C8BB2ABF8C4D01B7490290A1AA2BF95FC6D` |

The replayed TSV hash is identical to the candidate checked above. This establishes
that graph extraction is deterministic from the pinned compiled inputs and does not
depend on rebuilding or mutable package state.

## What this proves

| Requirement | Evidence |
| --- | --- |
| All 4,195 selected declarations preserved | `selected_declarations: 4195`; no missing-declaration diagnostic |
| Every incident edge preserved | 18,256 signature and 30,343 body edges match `P0002` exactly |
| All 32,459 distinct incident pairs preserved | the 48,599 kind-tagged edge entries contain 16,140 pairs carrying both signature and body edges; their union is 32,459, matching `P0002.json` |
| No kind drift | no kind-drift diagnostic |
| No visibility drift | no visibility-drift diagnostic |
| Every owner remains in the authorized scope | 73 exact modules and 65 prefixes accepted; no owner-not-allowed diagnostic |
| The physical migration occurred | 2,220 of 4,195 selected declarations relocated to new semantic leaves |

The checker compares declaration identities and incident edge sets, not merely their
counts. Passing therefore establishes exact equality for the selected semantic
projection, including declaration kind and visibility.

## Private-name preservation

W02 computed private seeds and their reverse user closure before reconstructing the
19 physical owners. Commands in that closure remain in their historical modules, so
Lean's module-qualified private names do not change. The delivery routes 258 selected
declarations to historical owners and relocates 2,220; the remaining 1,717 selected
declarations belong to the 54 modules classified canonical in place.

This is why the projection passes without promoting, renaming, or fabricating any
private declaration. A successful production build alone would not establish this
identity: the projection additionally verifies every selected name and every
incident signature/body edge against the frozen C0002 graph.
