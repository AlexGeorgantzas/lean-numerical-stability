# C0007 acceptance evidence

Checkpoint code commit: `9eb534a06db267203c2b9b88227edd44fc64f5db`

Accepted at: `2026-08-08T21:26:00Z`

## Remote gate

[GitHub Lean CI run 31276982723](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31276982723) completed successfully for the exact checkpoint code commit on the `main` push event. The job ran from `2026-08-08T20:28:24Z` to `2026-08-08T21:09:05Z`. Its architecture, phase-contract, layout, compatibility, provenance, and strict-source step completed successfully at `2026-08-08T20:31:55Z`. Its clean `lake build NumStability NumStabilityTest` step completed successfully at `2026-08-08T21:09:03Z`; the Lake log reported `Build completed successfully (8428 jobs)`.

## Delivery ancestry and scope

W04 delivery `12bd75d4d25b2d98344d26b0dc0b016f1e2f1814`, W09 delivery `69ee6cf790d1f3826075f33ea4907c9a4b5a637a`, and W11 delivery `580c0298a47a533725e034c32c7702a7436fa6ed` all descend from exact C0006 code commit `a32095e6e50189f7dcc39312bb4c6a36f421fab5`. They are ancestors of the checkpoint code commit through separate true Git merges `584d82372fd4f07fbcc5589321f99e363e5c94b0`, `3e9d6463739f04965cd7795994906604d0fe33a6`, and `77b268c2166eca392c92affff60f11234addcc11`.

The immutable W04 audit contains 253 paths: 29 historical owners, 84 canonical production modules, 124 tests, and 16 delivery-evidence files. W09 contains 366 paths: 72 historical owners, 93 canonical production modules, 191 tests, and 10 delivery-evidence files. W11 contains 146 paths: 18 historical owners, 37 canonical production modules, 76 tests, and 15 delivery-evidence files. The joint 765-path delivery scope therefore contains 119 owners, 214 canonical production modules, 391 tests, and 41 evidence files. Each audit covers every owned path and authorized destination with zero forbidden or unowned paths. The waves have zero owned-path overlap, zero destination-prefix ancestor/descendant overlap, and zero owner overlap.

The exact post-merge integration diff `77b268c2166eca392c92affff60f11234addcc11..9eb534a06db267203c2b9b88227edd44fc64f5db` contains 65 paths: 9 added request artifacts, 3 added test aggregates, 7 modified aggregates, 2 modified classification files, 34 modified consumers, 9 modified control files, and 1 modified evidence smoke test. Status totals are 12 added and 53 modified. The permanent path ledger is `C0007-integrator-paths.tsv`, SHA-256 `007FECE988156DE622788EA388CF4217FB71B560D6305436F560CA29E83A3C43`. No generated build artifact is tracked.

## Shared integration requests and overlap changes

R0007, R0008, and R0009 were independently based on exact C0006 code commit `a32095e6e50189f7dcc39312bb4c6a36f421fab5`. Their sorted patches, exact preimage rows, and hash-pinned overlap reviews were validated independently against disposable C0006 indexes. Each patch forward-replayed and reverse-replayed exactly. Unique postimages equal the integrated tree except for R0007's `NumStability/Algorithms/LinearSystems.lean`: the standalone patch postimage is blob `a2b03e35cf346c2e42510a4bd2aed09a0129d4e2`, while the integrated blob `fd3b04b44f419223d6470c2609552f63e42868fd` places the same requested import set before the unchanged module docstring as part of aggregate import normalization. Removing import commands leaves identical non-import text. Intersecting postimages were reconciled as deliberate unions.

- R0007 / W04: 8 paths; patch SHA-256 `5EB1ACF5C24D51ACB7F2FD6A258E8D53A2EFEBE09E77116539B4D85DE0D8114C`; review SHA-256 `596E8B563238224D3526D33DDA9E86A0A3E98014CEDD456C50BA6CD14F094D0A`.
- R0008 / W09: 6 paths; patch SHA-256 `BB602D4C854416DDA7F6FC7D69445093A53F496931718C34461BE476A32BF3AC`; review SHA-256 `D2F511E918A727608A76040F93FE0E8BB9C9D14980F3B2298AC54237CE05C556`.
- R0009 / W11: 7 paths; patch SHA-256 `E98E798A177831802DA9F36B1753EA1D31BDE707F17F0DF55E63D6DC6B4CDB68`; review SHA-256 `2460C49F645469BC0233C1D118FD6765A9500DE878DC3D65D564351D15321AD8`.

All three requests intersect on `NumStabilityTest.lean`, `tiers.json`, and `layout-exceptions.json`; R0007 and R0009 also intersect on `NumStability/Algorithms/LinearSystems/LeastSquares/Equality/Basic.lean`. The integrated Equality consumer atomically replaces both historical imports with the exact W04 pseudoinverse and W11 rank-factorization APIs. The tier union is exactly 214 additions with no removal or changed pre-existing value. The layout union removes 26 stale missing-docstring entries and adds only five reviewed W04 noncanonical-name entries. Test aggregates contain exactly 124 W04, 191 W09, and 76 W11 imports.

Every one of the 42 modified existing Lean files changes import commands only. Twenty-eight W04 canonical modules each drop one unused historical `NumStability.Algorithms.RandNLA.Preconditioning` import; this removes 28 direct W04-to-W11 facade edges and the resulting 196 strict-source reachability pairs. The integrated tree has zero canonical-to-historical reachability and zero reusable-to-Source reachability. W11 LowRankApprox preserves the three accepted MatrixInversion LU-factor/residual APIs and never restores the historical MatrixInversion umbrella. Accepted W02/W06 and Chapter 20 interfaces remain intact. W07, W10, W90, and all other accepted owners are untouched.

## Static and architecture gates

All commands below exited zero against the same integrated code tree:

- `python tools/architecture/check_phase.py --self-test`: the phase-contract fixture passed and every negative drift/tampering fixture was rejected.
- `python tools/architecture/check_phase_projection.py --self-test`: plain and deterministic-gzip fixtures passed; edge, owner, duplicate, and gzip drift were rejected.
- `python tools/architecture/check_phase.py`: the delivered/request state passed before C0007 publication.
- `python tools/architecture/check_layout.py`: 2,456 production modules; 309 unclassified, 9 mixed, 91 missing module docstrings, 266 noncanonical names, 21 declaration-bearing umbrellas, and zero unsorted aggregates.
- `python tools/architecture/check_compatibility.py`: 337 forwarding modules and 685 canonical targets.
- `python tools/architecture/check_provenance.py`: 139 Apache-marked production files and 5 evidenced upstream modules.
- Placeholder/axiom audit, enforced by the layout checker: zero `sorry`, `admit`, top-level `axiom`, or top-level `constant` commands.
- Import-graph audit: zero unresolved project imports, zero cycles, and zero reusable-to-Source reachability.
- Cross-wave audit: zero direct imports, signature edges, and body/proof edges in every direction among the three activation owner sets; the integrated destination tree likewise has zero cross-wave direct imports. `NumStability/Algorithms.lean` and `NumStability/Algorithms/LinearSystems/LeastSquares/Equality/Basic.lean` remain integrator-owned downstream consumers.

## Integrated Lean builds and tests

Every local Lean operation held Windows named mutex `Local\lean-reorganization-2026-08`; checkpoint JSON normalizes the lock name to `lean-reorganization-2026-08`. The exact test sets were ordinal-sorted, mutually disjoint, and hash-pinned before invocation.

| Gate | Exact test modules | Module-list SHA-256 | Jobs | Seconds | Exit |
| --- | ---: | --- | ---: | ---: | ---: |
| canonical-only | 214 | `C63934CA1AEC02A761AD3AA8711C352159E924A27EDFE32A5428D93A2A5C15F3` | 3,846 | 4.683 | 0 |
| old-path-only | 119 | `AD7956A2BD646F6C2C167CFC40F2088FB835F46D26B6F28056A0E6AE41599291` | 3,878 | 4.745 | 0 |
| focused/protected | 58 | `D7A54BBA2059F041F32256BE32BE38B8B27FE08B1E1B1B37E7438BE40C7F286F` | 3,786 | 4.708 | 0 |
| `lake test` | full test target | n/a | JSON job count null | 6.747 | 0 |

An additional build of the three W04/W09/W11 aggregate roots reached all 391 matrix-listed smoke modules and completed successfully with 4,171 jobs. A local exhaustive `lake build NumStability NumStabilityTest` also completed successfully with 8,428 jobs before the code commit; the remote gate independently rebuilt the same two roots from a clean checkout.

## Strict source and projection replay

Exact-commit strict-source generation ran under the mutex and exited zero in 17.211 seconds, with zero cycles and zero forbidden reusable-to-Source reachability. Its ignored JSON and Markdown evidence have SHA-256 `81D144213878E57A3D73736CC0A99D60E4E758F6C251A5378D7B66826D2A4C0D` and `787F940B8EE5AA199246F5365683FAFEA94B37198D90580292C5FE38BBD33F70`.

The official C0007 format-2 candidate scanned 56,903 declarations and 649,259 typed edge rows and has raw TSV SHA-256 `80AE3FBB3948104C60FF7EA80E899CC11CE542D0A772EA087375C00EB0ED9ED3`. Before replay, the checker, selectors, projections, C0006 inventory, and C0006 baseline hashes pinned by P0009, P0010, and P0011 were verified. The exact recorded checker arguments were replayed with only the candidate placeholder replaced:

| Projection | Selected | Relocated | Retained | Signature edges | Body/proof edges | Union edges | Exit |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| P0009 / W04 | 1,238 | 1,018 | 220 | 5,684 | 10,044 | 10,624 | 0 |
| P0010 / W09 | 1,865 | 1,295 | 570 | 3,639 | 7,414 | 7,721 | 0 |
| P0011 / W11 | 3,354 | 3,129 | 225 | 19,096 | 26,201 | 28,652 | 0 |

W04's exact retained private reverse closure is 220 declarations: 40 private plus 180 public. Its declaration-mixed owners were routed narrowly between reusable underdetermined APIs and exact Chapter 21 source endpoints. W09 retains 570 declarations; its preliminary private reverse-closure floor was 423 (165 private plus 258 public), enlarged by local ambient/compiler closure. The three mixed Higham28 owners were split declaration-by-declaration, the accepted Jordan primary-decomposition route was preserved, and W10's historical import surface was not edited. W11's exact retained closure is 225 declarations from three disjoint private roots (3 private plus 222 public). ElementwiseSpectral and LowRankApprox were routed declaration-by-declaration; the Chapter 20-dependent LeastSquaresSketch closure remains source-side, so no reusable module depends on Source.

## Official C0007 combined baseline

The official extractor ran from the clean checkpoint code commit under the same named mutex:

`python tools/architecture/generate_baseline.py --output-dir docs/architecture/phases/2026-08-repository-reorganization/baselines --name C0007-combined --keep-dependency-tsv benchmark-results/C0007-combined.tsv`

It completed 6,002 Lean extraction jobs and deterministic graph validation with exit zero in 384.614 seconds. It records `library_source_clean: true`, an empty `library_source_dirty_paths` list, format version 2, and exact commit `9eb534a06db267203c2b9b88227edd44fc64f5db`. The capture contains 2,456 production modules, 3,862,736 source lines, 1,444,162 nonblank lines, 74,027,573 bytes, 23,952 direct imports (15,051 internal and 8,901 external), 56,903 declarations, 266,387 signature edges, 382,872 body/proof edges, and 424,082 union edges.

- JSON SHA-256: `D9372A79DA159CEB50757F6581F650957D2868E738E41C0D5F892C121623CADD`
- Markdown SHA-256: `A9C897F4E2EDCDE3B3CAFE5D297B11A05E5D20BA5CC2AF3BD746C90D02F5D3AC`
- Raw dependency TSV SHA-256: `80AE3FBB3948104C60FF7EA80E899CC11CE542D0A772EA087375C00EB0ED9ED3`
- Source-tree SHA-256: `9E600969A7D33615AEC3272E9C4063C89B1F5C73A008D10E972525D9595CF527`
- C0007 inventory SHA-256: `56B08C666F4461BE2B425E12B2E250ACFCD4604A43F793A066AA086091365196`
- C0007 integrator-path ledger SHA-256: `007FECE988156DE622788EA388CF4217FB71B560D6305436F560CA29E83A3C43`

## Acceptance and retirement boundary

C0007 accepts M04, M09, and M11 at the green code commit. M10 becomes ready; M07 remains ready and unactivated; M90 remains planned. C0006 remains the historical parent and C0007 becomes current. B0008, B0009, and B0010 become accepted with retirement due; P0009, P0010, and P0011 become retired immutable evidence; R0007, R0008, and R0009 become applied.

The three exact remote delivery refs and the W09/W11 local delivery worktrees remain present until the C0007 acceptance-control commit itself passes Lean CI. Only after that green control commit may the refs be atomically deleted with exact-SHA leases, ignored worker artifacts be preserved, and the two local worktrees be removed without force in a separate retirement step. Local worker branches remain preservation targets. W04 never had a local worktree. W07 was not activated, and no W07, W10, or W90 source migration was performed.
