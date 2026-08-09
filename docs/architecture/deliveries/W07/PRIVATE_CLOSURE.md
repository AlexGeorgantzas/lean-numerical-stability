# W07 private-declaration reverse closure

W07 contains exactly eight private declarations.  All remain in
`NumStability.Algorithms.StationaryIteration` under their original generated
private names; none is moved, renamed, duplicated, or promoted:

1. `_private.NumStability.Algorithms.StationaryIteration.0.NumStability.geom_partial_sum_le`
2. `_private.NumStability.Algorithms.StationaryIteration.0.NumStability.matMul_matSub_id_left`
3. `_private.NumStability.Algorithms.StationaryIteration.0.NumStability.matMul_matSub_id_matSub_id`
4. `_private.NumStability.Algorithms.StationaryIteration.0.NumStability.matMul_matSub_id_right`
5. `_private.NumStability.Algorithms.StationaryIteration.0.NumStability.residualSigmaTsum_entry_le_of_real_diagonalization`
6. `_private.NumStability.Algorithms.StationaryIteration.0.NumStability.residual_geometric_partial_le_ratio`
7. `_private.NumStability.Algorithms.StationaryIteration.0.NumStability.residual_term_entry_abs_le_of_real_diagonalization`
8. `_private.NumStability.Algorithms.StationaryIteration.0.NumStability.singularErrorSourceTerm_term_eq`

## Exact graph closure

The deterministic W07-selected dependency graph combines all P0012 signature
and body/proof edges.  Starting from the eight private seeds, reverse traversal
retains every selected declaration that directly or transitively depends on a
seed.  The result is exactly the 31-declaration preliminary floor required by
P0012:

| Owner | Private seeds | Public dependents | Graph floor |
| --- | ---: | ---: | ---: |
| `StationaryIteration` | 8 | 21 | 29 |
| `StationaryIterationDrazin` | 0 | 2 | 2 |
| **Total** | **8** | **23** | **31** |

The eight seeds have depth 0.  The 23 public dependents have one deterministic
body/proof witness each: eight at depth 1, nine at depth 2, four at depth 3,
and two at depth 4.  No signature-only witness is lost; the combined traversal
examines both typed edge classes even though the selected witness forest happens
to use body/proof edges for all 23 non-seed nodes.

`PRIVATE_CLOSURE.tsv` records every source command span, decision, closure
depth, witness owner and command root, edge kind, source declaration, target
declaration, and selected declarations carried by the command.  `RETENTION.tsv`
records the same result one retained declaration at a time.

The ordered 31-declaration floor payload has SHA-256:

`6A1B37537E0002E89B1B88F2BED03C6F7A701936A237FF33A49DFBD58E76E2B7`

## Actual retention

The compiler requires no additional ambient command beyond the exact 31-node
graph floor.  The actual historical retention is nevertheless 116
declarations because B0011 forbids physical movement from the four
classify/document-only owners:

| Retention reason | Declarations |
| --- | ---: |
| Private seeds | 8 |
| Public reverse-closure dependents | 23 |
| Classify/document-only declarations outside the graph floor | 85 |
| **Actual retained total** | **116** |

The Drazin owner contributes two declarations to the graph floor and 39 other
classify/document-only declarations; Rounded, Semiconvergent, and
SemiconvergentExistence contribute 16, 20, and 10 classify/document-only
declarations respectively.  Thus the four companion owners retain all 87 of
their declarations while the `StationaryIteration` facade retains exactly its
29-node portion of the private closure.

`CHECK_STATIC.py` independently checks the eight exact seeds, 31-node floor,
116 actual retentions, payload hash, every witness, facade shape, and agreement
among `PRIVATE_CLOSURE.tsv`, `RETENTION.tsv`, and
`DECLARATION_ROUTES.tsv`.  Old-path and focused private-retention tests compile
the declaration-bearing facade directly.
