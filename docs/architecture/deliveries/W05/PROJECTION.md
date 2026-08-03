# W05 projection result — P0006

The W05 candidate is compared with the active `P0006.tsv.gz` projection using only
the exact modules, destination prefixes, checker arguments, and hashes recorded in
`P0006.json`.

| Artifact | SHA-256 |
| --- | --- |
| `tools/architecture/check_phase_projection.py` | `29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443` |
| `P0006.tsv.gz` | `6A15BC343C895BCE66A92B09EC333300CA842BEC249DDF2DC723D0832098FFB5` |
| full W05 candidate TSV | `89E4BEE5E541E5AD4DD2F386282DAD2F920D7013194A0ECBBE5CB67722FBE89D` |
| no-build replay TSV | `89E4BEE5E541E5AD4DD2F386282DAD2F920D7013194A0ECBBE5CB67722FBE89D` |

Both pinned control artifacts were hash-verified before the checker ran.  The
candidate placeholder in the recorded P0006 arguments was replaced with the
absolute worker path
`C:\Users\qed_s\higham-worktrees\reorg-w05-codex\benchmark-results\W05-candidate.tsv`;
no other argument changed.

## Expected projection

| Quantity | P0006 value |
| --- | ---: |
| Selected declarations | 921 |
| Definitions | 121 |
| Theorems | 800 |
| Signature edges | 8,562 |
| Body/proof edges | 6,894 |
| Union edges | 11,020 |

## Locked extraction and comparison

The full candidate generation held `Local\lean-reorganization-2026-08` and produced
the complete format-2 dependency graph from the worker tree after
`Build completed successfully (5292 jobs)`.

```text
phase projection contract passed
projection_sha256: 6A15BC343C895BCE66A92B09EC333300CA842BEC249DDF2DC723D0832098FFB5
candidate_sha256: 89E4BEE5E541E5AD4DD2F386282DAD2F920D7013194A0ECBBE5CB67722FBE89D
selected_declarations: 921
relocated_declarations: 783
signature_edges: 8562
body_edges: 6894
candidate_declarations_scanned: 56903
candidate_edges_scanned: 649259
allowed_exact_modules: 10
allowed_prefixes: 14
checker_exit: 0
```

The checker compares declaration identity, kind, visibility, owner scope, and every
incident signature/body edge—not merely the aggregate counts.  A pass therefore
establishes that every P0006 declaration and typed dependency was preserved.

## Deterministic replay

After the full candidate extraction, `generate_baseline.py --no-build` was run under
the same mutex into a separate output directory.  The replay result was:

```text
TSV       candidate = replay = 89E4BEE5E541E5AD4DD2F386282DAD2F920D7013194A0ECBBE5CB67722FBE89D
JSON      candidate = replay = 4AFAD18974AEDD90B86F51C757ACB66AC93C4AEA7C8343C66458195113D0DCD7
Markdown  candidate = replay = C7E56C4B8C0D2E8CD4BFA9344499F102D6A0ACDF698C27818EE8BB4102855B24
candidate exit: 0
no-build replay exit: 0
```

## Relocation proof

The declaration ledger routes 783 declarations to new semantic/source leaves and
retains 138 in `NumStability.Algorithms.Sylvester.Higham16`.  The retained set is the
exact reverse closure of the three module-qualified private seeds.  P0006's exact
comparison is the final proof that this physical split preserves all 921 declaration
identities and their 8,562 signature plus 6,894 body/proof incident edges.
