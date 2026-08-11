# R01 private reverse closure

The active B0001/P0001 authority freezes **10 private declarations** and their complete
selected full-graph reverse closure. The exact control payload is reproduced byte-for-byte
as `PRIVATE_CLOSURE.tsv` (SHA-256
`CB19F5F3C66C56CE5F688E5E310D64713834635AFDFB77D7CB24DC1EC9D88598`).

## Exact accounting

| class | count |
| --- | ---: |
| approved private seeds | 10 |
| public reverse dependents | 32 |
| complete reverse closure | 42 |
| private declarations promoted | 0 |
| private declarations omitted | 0 |
| independent private renames | 0 |

Unlike predecessor waves that retained private closures at historical owners, P0001
explicitly supplies the reviewed normalization map. All ten private declarations move
with their dependent public declarations and acquire only the module-encoded private
name approved before activation:

| destination | private count |
| --- | ---: |
| `Algorithms...Semiconvergence.Projectors.FixedRange` | 3 |
| `Analysis...MatrixPowers.Semiconvergence.TriangularBlockForm` | 2 |
| `Source...Results.Equation20.DiagonalizableBounds` | 4 |
| `Source...Results.Equation29.SingularBounds` | 1 |

The 42-row closure is distributed across eight baseline owners: 29 rows from
`Algorithms.StationaryIteration`, four from
`Analysis.SemiconvergentBlockFormExists`, two each from the Drazin owner,
the real-spectrum owner, and the protected Equation22 consumer, and one each from
the primary-splitting owner, general-limit owner, and historical Equation20 owner.

`RETENTION.tsv` records the expected candidate name for every selected declaration:
all 233 public names remain byte-identical, while exactly these ten private names use the
approved map. `CHECK_STATIC.py` checks the closure roster and
`CHECK_PROJECTION.py` replays P0001 with the same private-map hash.
