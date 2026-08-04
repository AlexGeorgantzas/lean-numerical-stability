# C0006 acceptance evidence

Checkpoint code commit: `a32095e6e50189f7dcc39312bb4c6a36f421fab5`

Accepted at: `2026-08-04T13:15:16Z`

## Remote gate

[GitHub Lean CI run 30904834867](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/30904834867) completed successfully at the exact checkpoint code commit. The job ran from `2026-08-04T11:26:53Z` to `2026-08-04T12:56:33Z`. Its architecture, phase-contract, layout, compatibility, provenance, and strict-source step completed successfully at `2026-08-04T11:30:35Z`; its clean `lake build NumStability NumStabilityTest` step completed successfully at `2026-08-04T12:56:29Z`.

## Delivery ancestry and scope

W06 delivery `436b38cbda2e06cf5c9ea3343f0bc6fe428f0b97` and W08 delivery `664d5d495975a05d74cd4c0c09f9207aff8cdd77` are ancestors of the checkpoint code commit through separate true Git merges. Each immutable delivery has the exact C0005 code commit `240c0d041781385a647fbec461d6863537e562cb` as its sole parent.

W06's immutable base-to-delivery audit contains 518 paths: 67 historical owners, 176 canonical production modules, 257 tests, and 18 delivery-evidence files. W08's immutable audit contains 250 paths: 42 historical owners, 73 canonical production modules, 125 tests, and 10 delivery-evidence files. Both audits cover every owned path and authorized destination with zero forbidden or unowned paths. The waves have zero changed-path, owner, and destination overlap; zero direct imports; and zero declaration-signature or declaration-body/proof edges between them.

The exact post-merge integration diff `50a5893fa21cfccbdf801e5378d09ab05a524e9a..a32095e6e50189f7dcc39312bb4c6a36f421fab5` contains 190 paths: 153 production aggregates (134 added and 19 modified), 2 added test aggregates, 6 request artifacts, 19 modified consumers, 3 classification files, 6 control files, and 1 corrected delivery-evidence file. The permanent path ledger is `C0006-integrator-paths.tsv`, SHA-256 `2C8B25CB5E1ED072CC4506886D91EE9F35A8BA5522348F36D3172DCB32BEFA00`. No generated build artifact is tracked.

## Shared integration requests and overlap changes

R0005 and R0006 were independently based on exact C0005 code commit `240c0d041781385a647fbec461d6863537e562cb`. Their sorted patches and exact preimage rows were validated independently against disposable C0005 indexes:

- R0005: 73 paths; patch SHA-256 `C7F94237B46745BFAC501780D806499431CECBFBDBFA7B70798E801716115D42`.
- R0006: 76 paths; patch SHA-256 `54693108C1627E5DA067B16A520D009EFCCEEE2A2D81930B756CD5A69B6D9504`.

The integrated tree contains every accepted umbrella, root-test, tier, compatibility, layout-exception, discovery, and consumer-retarget change. Five future-wave owners received only their exact reviewed import-line changes. The three W07 files `StationaryIteration.lean`, `StationaryIterationDrazin.lean`, and `StationaryIterationSemiconvergent.lean` now import `NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealDiagonal` instead of the historical MatrixPowers facade. W11's `RandNLA/LowRankApprox.lean` now imports the three exact reusable MatrixInversion LU-factor/residual modules instead of the historical MatrixInversion facade. All declarations and typed edges remain unchanged. W07 and W11 must refresh from C0006. No W04, W07, W09, W10, or W11 source migration was performed.

## Static and architecture gates

All commands below exited zero against the same fully integrated code tree:

- `python tools/architecture/check_phase.py --self-test`: phase-contract self-test passed.
- `python tools/architecture/check_phase.py`: C0005-era active-control state passed before C0006 publication.
- `python tools/architecture/check_layout.py`: 2,242 production modules; 309 unclassified, 9 mixed, 117 missing module docstrings, 261 noncanonical names, 21 declaration-bearing umbrellas, and zero unsorted aggregates.
- `python tools/architecture/check_compatibility.py`: 337 forwarding modules and 685 canonical targets.
- `python tools/architecture/check_provenance.py`: 197 Apache-marked production files and 5 evidenced upstream modules.
- Placeholder/axiom audit: zero new `sorry`, `admit`, top-level `axiom`, or declaration weakening.
- Import-graph audit: zero unresolved project imports, zero cycles, and zero reusable-to-Source reachability.
- Aggregate/import sorting audit: zero unsorted aggregate imports.
- Integration-overlap audit: the five W07/W11 files changed only in import lines; no other W04/W07/W09/W10/W11 owner changed.

## Integrated Lean builds and tests

Every local Lean operation held Windows named mutex `Local\lean-reorganization-2026-08`; the checkpoint records normalized lock name `lean-reorganization-2026-08`. Actual results were:

| Gate | Modules | Jobs | Seconds | Exit |
| --- | ---: | ---: | ---: | ---: |
| W06 canonical-only | 176 | 4,087 | 2,759.714 | 0 |
| W06 old-path-only | 67 | 3,994 | 559.149 | 0 |
| W06 focused | 14 | 3,974 | 283.240 | 0 |
| all W06 test modules explicitly | 257 | 4,351 | 6.122 | 0 |
| `NumStabilityTest.Reorganization.W06` | 1 aggregate | 4,352 | 25.227 | 0 |
| W08 canonical-only | 73 | 3,263 | 593.227 | 0 |
| W08 old-path-only | 42 | 3,274 | 342.270 | 0 |
| W08 focused | 10 | 3,226 | 44.611 | 0 |
| all W08 test modules explicitly | 125 | 3,357 | 4.691 | 0 |
| `NumStabilityTest.Reorganization.W08` | 1 aggregate | 3,358 | 19.794 | 0 |
| protected W02/W05/W07/W09/W10/W11 surfaces | 24 | 4,097 | 5.127 | 0 |
| W07/W11 overlap files | 4 | 3,399 | 4.638 | 0 |
| `lake build NumStability` | 1 root | 5,788 | 3,555.672 | 0 |
| `lake build NumStability NumStabilityTest` | 2 roots | 7,820 | 3,284.695 | 0 |
| `lake test` | full test target | 7,818 scheduled | 11.130 | 0 |

`lake test` records a null JSON job count; the command scheduled 7,818 jobs and its log reached 7,815/7,818 before its zero exit.

## Strict source and projection replay

Strict-source format-2 generation exited zero in 16.936 seconds, with zero cycles and zero forbidden reusable-to-Source reachability. One full integrated format-2 candidate was used for both projection replays. It scanned 56,903 declarations and 649,259 typed edge rows, completed in 157.904 seconds, and has raw TSV SHA-256 `3BFEFF5663DA3FB5327B9D3AB22806654C9A79A48E1DDFE3C6E2E79073F9DE11`.

Before replay, the checker, selectors, projections, inventory, C0005 baseline, and raw-graph hashes pinned by P0007 and P0008 were verified. The exact recorded checker arguments were replayed with only the candidate placeholder replaced:

| Projection | Selected | Relocated | Retained | Signature edges | Body/proof edges | Union edges | Exit |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| P0007 / W06 | 3,512 | 2,737 | 775 | 15,044 | 16,341 | 22,079 | 0 |
| P0008 / W08 | 2,179 | 1,994 | 185 | 9,266 | 15,315 | 16,573 | 0 |

W06 retains 775 declarations (94 private and 681 public) across 23 declaration-bearing historical facades; its other 44 historical owners are pure import shims. The retained set includes the 768-declaration graph floor plus seven context/compiler-pinned declarations. W08 retains 185 declarations (45 private and 140 public) across 18 declaration-bearing historical facades; its other 24 historical owners are pure import shims. Its retained set includes the 179-declaration graph floor plus six command/compiler-pinned declarations.

## Official C0006 combined baseline

The official extractor ran from the clean checkpoint code commit under the same named mutex:

`python tools/architecture/generate_baseline.py --output-dir docs/architecture/phases/2026-08-repository-reorganization/baselines --name C0006-combined --keep-dependency-tsv benchmark-results/C0006-combined.tsv`

It completed 5,788 Lean jobs with exit zero in 229.101 seconds; validation exited zero in 22.152 seconds. It records `library_source_clean: true`, an empty dirty-path list, and exact commit `a32095e6e50189f7dcc39312bb4c6a36f421fab5`. The capture contains 2,242 production modules, 3,275,409 source lines, 1,432,575 nonblank lines, 72,841,048 bytes, 16,654 direct imports (11,206 internal and 5,448 external), 56,903 declarations, 266,387 signature edges, 382,872 body/proof edges, and 424,082 union edges.

- JSON SHA-256: `E9207AA896EAA547E791FB1CECAC7A6B4E6344E8DC8E15D2EF2372FF90570625`
- Markdown SHA-256: `59E7098C61B39A21B1A5E1EFF3E6D2F3CD4FACC703549A0293FB9E13325D8EE6`
- Raw dependency TSV SHA-256: `3BFEFF5663DA3FB5327B9D3AB22806654C9A79A48E1DDFE3C6E2E79073F9DE11`
- Source-tree SHA-256: `097CDCDE45D5E8EA5A4C0FD85A5C85E1410F932B7CBD2F5A15127D5DE716FD25`
- C0006 inventory SHA-256: `5A8C01FE644CC2DD1190E2DDFEFBAD0EE16D01BD5F7863086E7D2DE5EE307FCC`

## Acceptance and retirement boundary

C0006 accepts M06 and M08 at the green code commit. M04, M07, M09, and M11 are ready but are not activated; M10 and M90 remain planned. B0006 and B0007 are accepted with retirement due until the acceptance-control commit itself passes Lean CI. Only after that green control commit may the two exact remote delivery refs be atomically deleted with expected-SHA leases and their retirement recorded. Local worktrees and local branches remain preserved.
