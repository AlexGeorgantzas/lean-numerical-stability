# W06 projection result - P0007

The W06 candidate is compared with the active `P0007.tsv.gz` projection using
only the exact owner modules, 49 reviewed destination prefixes, checker
arguments, and hashes recorded in `P0007.json`.

## Pinned artifacts

| Artifact | SHA-256 |
| --- | --- |
| `tools/architecture/check_phase_projection.py` | `29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443` |
| `selectors/W06.tsv` | `5D482CF32C656C77AF3AABA674C3FE39AA5AEBD0FED6BC0C3E569DCDB328E484` |
| `P0007.tsv.gz` | `E1C2787CC0D0D8A08E016932CEBC1831FAD6929BF22FA757D12BFC49F8ADCF39` |
| C0005 combined baseline JSON | `D961829AA197564A94193B9909695E6DA077D02B64F07EFC6FC531BB291EF190` |
| C0005 raw format-2 graph | `1DA19910927D41F4B45266ABA3F5E1A1F165637F7E984F8A19E15DA4FBB4A8D0` |
| full W06 candidate TSV | `7A312F60BDA611BBEB7DDF8060A9C360172DC945C91800B4C5D888A11C447B47` |
| candidate JSON | `A54DF4F3D684979761490383046AB1A7B4989FB9CDC4981E45A6DBF418FA9DD6` |
| candidate Markdown | `730E06CB87F101F8A9299E9F21D6B0404D771608E7F4912065FF68A445A9C5D9` |
| private-closure TSV | `5391A2EAED68263FE9EE2B38D35F79A1660BF06728580D37485286CC115B0E64` |

`CHECK_PROJECTION.py` verifies every pinned control hash before invoking the
recorded checker argument vector.  It replaces only the candidate placeholder
with the absolute worker path
`C:\Users\qed_s\higham-worktrees\reorg-w06-codex-remote\benchmark-results\W06-candidate.tsv`.
It does not add, remove, reorder, or broaden an `--allow-module` or
`--allow-prefix` argument.

## Expected projection

| Quantity | P0007 value |
| --- | ---: |
| Selected declarations | 3,512 |
| Theorems | 3,180 |
| Definitions | 317 |
| Inductives / constructors / recursors | 5 / 5 / 5 |
| Public / private declarations | 3,418 / 94 |
| Signature edge rows | 15,044 |
| Body/proof edge rows | 16,341 |
| Union edges | 22,079 |

## Candidate extraction

After the final library and test builds, the full format-2 candidate was
extracted under `Local\lean-reorganization-2026-08` from the same worker tree.
The source scan covered 2,035 Lean modules with zero unresolved imports and zero
import cycles.  The declaration extractor scanned 56,903 declarations and
649,259 typed edge rows.  Candidate generation exited 0.

The exact P0007 replay returned:

```text
phase projection contract passed
projection_sha256: E1C2787CC0D0D8A08E016932CEBC1831FAD6929BF22FA757D12BFC49F8ADCF39
candidate_sha256: 7A312F60BDA611BBEB7DDF8060A9C360172DC945C91800B4C5D888A11C447B47
selected_declarations: 3512
relocated_declarations: 2737
signature_edges: 15044
body_edges: 16341
candidate_declarations_scanned: 56903
candidate_edges_scanned: 649259
allowed_exact_modules: 67
allowed_prefixes: 49
retained_declarations: 775
union_edges: 22079
checker_exit: 0
```

The checker compares declaration identity, kind, visibility, owner scope, and
every incident signature/body edge.  The pass therefore proves preservation of
all 3,512 selected declarations and all 31,385 typed incident edge rows, not
merely the aggregate counts.

## Relocation and retention

The declaration ledger routes 2,737 declarations to new destinations: 2,114 to
reusable APIs and 623 to exact Chapter 16/18 source leaves.  It retains 775
declarations in 23 historical owners.  All 94 private declarations are retained.

The P0007 reverse-closure computation produces a 768-declaration graph floor:
94 private and 674 public declarations.  Seven additional public commands are
retained with `Higham16Problem16_2` because their notation and section context
cannot be separated safely.  The final 775 count agrees exactly across
`DECLARATION_ROUTES.tsv`, `RETENTION.tsv`, the generated tree, and the checker.

## Deterministic replay

The frozen candidate TSV was summarized again under the mutex without invoking
Lean.  The replay exited 0 and reproduced both reports byte-identically:

```text
JSON      candidate = replay = A54DF4F3D684979761490383046AB1A7B4989FB9CDC4981E45A6DBF418FA9DD6
Markdown  candidate = replay = 730E06CB87F101F8A9299E9F21D6B0404D771608E7F4912065FF68A445A9C5D9
```

## Source-tier boundary

The W06 canonical graph audit passes with zero reusable canonical-to-Source
reachability.  The repository-wide `--strict-source` scan exits 2 on 31 paths
that originate in accepted reusable consumers and pass through historical W06
facades still imported by forbidden accepted/future owners.  Twelve pass
through the explicitly deferred W07 `StationaryIterationSemiconvergent` surface.
There are zero unresolved imports, zero cycles, and zero reusable-to-mixed paths.
`INTEGRATOR_REQUESTS.md` records the exact integration and later-W07 retargets;
no P0007 mismatch or worker-owned graph defect is waived.
