# R11 projection replay — P0003

The frozen P0003 projection was replayed against the R11 worker candidate with the
exact argument vector the P0003 record lists, under
`Local\lean-reorganization-2026-08`. `CHECK_PROJECTION.py` reproduces that vector,
diffs it against the record, and refuses to run if either side has drifted.

## Pinned inputs

| artifact | SHA-256 |
| --- | --- |
| `projections/P0003.tsv.gz` | `31EC591D949DB6041078C036F0CFF74A0A3EE229B35E351DDF999D15F494D60E` |
| `branches/B0003-private-normalization.tsv` | `12E4D4F517D3678DABA4A11F57D36E22EE4428BC3598D3CA0FC7E41A9323E70E` |
| `tools/architecture/check_completion_phase_projection.py` | `0F32935ED1EFDD2BD4D6A4C346F3E8300C86DB1D4A3551A17165479226109220` |

All three were verified before use. The controls were read from a read-only control
checkout at the active-control commit `5e075b947a63e84c784afecd00e1f130e21ea659`,
because B0003/P0003/R0003 are deliberately absent from the C0001 worker branch and
were not merged into it.

## Candidate

| quantity | value |
| --- | ---: |
| path | `benchmark-results/R11-candidate.tsv` |
| bytes | 116,736,010 |
| SHA-256 | `FBF9B388DF9107D99A64B5427066C38E6325ACFC788731207A14E546D090C3F9` |
| total rows | 706,163 |
| declaration rows | 56,903 |
| candidate gate exit | 0 |
| deterministic re-summary exit | 0 |

The candidate is a full format-2 declaration graph for the whole repository, not a
projection of it. Re-summarizing the same TSV reproduced identical JSON/Markdown
output, which is what makes the extraction deterministic rather than merely repeatable.

## Replay result

```text
phase projection contract passed
projection_sha256: 31EC591D949DB6041078C036F0CFF74A0A3EE229B35E351DDF999D15F494D60E
candidate_sha256: FBF9B388DF9107D99A64B5427066C38E6325ACFC788731207A14E546D090C3F9
selected_declarations: 1477
relocated_declarations: 412
signature_edges: 15172
body_edges: 18056
candidate_declarations_scanned: 56903
candidate_edges_scanned: 649259
allowed_exact_modules: 65
allowed_prefixes: 3
private_map_sha256: 12E4D4F517D3678DABA4A11F57D36E22EE4428BC3598D3CA0FC7E41A9323E70E
private_normalizations: 17
```

| requirement | frozen | observed |
| --- | ---: | ---: |
| selected declarations | 1477 | 1477 |
| signature edges | 15172 | 15172 |
| body/proof edges | 18056 | 18056 |
| relocated declarations | 412 | 412 |

The checker also reports `private_normalizations: 17`.
The tracked map has 17 rows and is total over all 17 selected private declarations:
16 module-prefix rewrites plus the `Chapter19.Core` identity row. The count above is
whatever the checker itself counts as normalized and is reported as measured rather
than asserted against a number this wave chose.

The union count is 19,873. As the checker compares the kind-tagged incident edge
set, 15,172 signature + 18,056 body = 33,228 entries collapse to 19,873 distinct
source→target pairs once the 13,355 pairs carrying both a signature and a body edge
are counted once. Both figures match P0003's `expected_counts`.

1,065 of the 1,477 declarations are retained rather than relocated: the reviewed
`Chapter19.Core` source outlier. 412 relocated + 1,065 retained = 1,477.

## Why the private map is supplied here and not at C0001

Lean encodes the defining module inside a private name, so relocating a private
declaration renames it. `reviews/R11-R12-projection-replay.md` records that the
C0001 preimage replay deliberately omitted the two `--private-map` arguments,
because before delivery the private names are still the projection names. At
delivery the map must be supplied: without it, all 16 relocated privates read as
missing declarations and every one of their incident edges reads as a missing edge.

The comparison is exact set equality on incident edges, not a count. Passing means
the frozen graph and the candidate agree edge for edge.

Replay exit: 0 — contract passed. Measured seconds: 4.677.

## Timing note

The system clock stepped backwards by roughly 4.5 hours while the full production
build was running, so that gate's measured elapsed time is negative and is reported
as not measurable in `GATE_RESULTS.tsv` rather than as a fabricated duration. Exit
codes and Lake's own job summaries are unaffected: the library build reported
`Build completed successfully (6138 jobs)` with zero `error:` lines.
