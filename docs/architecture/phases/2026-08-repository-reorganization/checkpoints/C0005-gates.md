# C0005 acceptance evidence

Checkpoint code commit: `240c0d041781385a647fbec461d6863537e562cb`

Accepted at: `2026-08-03T15:09:38Z`

## Remote gate

[GitHub Lean CI run 30823069012](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/30823069012) completed successfully at the exact checkpoint code commit. The job ran from `2026-08-03T14:31:13Z` to `2026-08-03T15:05:09Z`. Its architecture, phase-contract, layout, compatibility, provenance, and strict-source step completed successfully at `2026-08-03T14:34:38Z`; its clean `lake build NumStability NumStabilityTest` step completed successfully at `2026-08-03T15:05:06Z`.

## Delivery ancestry and scope

W03 delivery `a36ea332cb8e19ed4f6985d1a22e8e356c5dc9ce` and W05 delivery `23883bb9e477a2645ce76213687c73584651c077` are ancestors of the checkpoint code commit through separate true Git merges. W03's immutable base-to-delivery audit contains 181 paths: 26 exact historical owners, 61 canonical production modules, 87 tests, and 7 delivery-evidence files. It covers 26/26 owned paths and 34/34 destination prefixes with zero forbidden or unclassified paths. W05's immutable audit contains 193 paths: 10 exact historical owners, 79 canonical production modules, 92 tests, and 12 delivery-evidence files, with zero forbidden or unowned paths.

The waves have zero owned-path overlap, zero destination overlap, zero direct imports, zero declaration-signature edges, and zero declaration-body/proof edges between them. Their only common downstream aggregate is integrator-owned `NumStability/Algorithms.lean`. No W04, W06, or W08 source owner was migrated. The exact intake-to-code-checkpoint diff contains 469 paths (375 additions and 94 modifications): 174 W03 worker payload paths, 181 W05 worker payload paths, and 114 integrator-owned paths. No generated build artifact is part of the commit.

## Shared integration requests

R0003 and R0004 were independently based on C0004 code commit `b56f609f3bf66b5d7d0b677567cce82fee0c275b`. Their sorted patches and exact preimage rows were validated against disposable C0004 indexes before application:

- R0003: 47 paths; patch SHA-256 `8AABF97189D3788AA6D6FA79A03810500507A46E9F5CE78091E71D862BB93476`.
- R0004: 27 paths; patch SHA-256 `65064084E1F5B53F4C6CD8C59802D9B443DFB05A5BCCA4682544E4AA74F710CC`.

The integrated tree contains every accepted umbrella, root-test, tier, compatibility, layout-exception, discovery, and consumer-retarget change. The 34 W03 production consumer retargets were checked against the actual integrated import graph; the two auxiliary diagnostic paths were not miscounted as production consumers. W05 preserves all 13 direct W06-to-W05 imports and all 8,161 frozen typed W06-to-W05 declaration edges. The accepted W02 consumer `NumStability.Analysis.SemiconvergentExistenceFull` uses the canonical real-Schur API. The nine pure W05 historical owners remain temporarily unclassified rather than compatibility because the frozen W06 consumers and required mixed discovery aggregate still import them; promoting them before W06 would violate the compatibility gate. This reviewed deferral is recorded in `COMPATIBILITY.md` and keeps every global gate green without editing W06.

## Static and architecture gates

All commands below exited zero against the same fully integrated code tree:

- `python tools/architecture/check_phase.py --self-test`: phase-contract self-test passed.
- `python tools/architecture/check_phase.py`: 5 checkpoints, 13 milestones, 5 branch records, 4 shared requests, and 6 baseline projections passed before C0005 publication.
- `python tools/architecture/check_layout.py`: 1,859 production modules; 309 unclassified, 9 mixed, 173 missing module docstrings, 259 noncanonical names, 17 declaration-bearing umbrellas, and zero unsorted aggregates.
- `python tools/architecture/check_compatibility.py`: 337 forwarding modules and 685 canonical targets.
- `python tools/architecture/check_provenance.py`: 200 Apache-marked production files and 5 evidenced upstream modules.
- Placeholder/axiom audit: zero `sorry`, `admit`, top-level `axiom`, or top-level `constant` commands.
- Import-graph audit: zero unresolved project imports, zero cycles, zero reusable-to-Source reachability, and zero reusable-to-mixed reachability.
- Aggregate/import sorting audit: zero unsorted aggregate imports.

## Integrated Lean builds and tests

Every local Lean operation held Windows named mutex `Local\lean-reorganization-2026-08`; the checkpoint records the normalized lock name `lean-reorganization-2026-08`. Actual results were:

| Gate | Modules | Jobs | Exit |
| --- | ---: | ---: | ---: |
| W03 canonical-only | 61 | 3,632 | 0 |
| W03 old-path-only | 26 | 3,617 | 0 |
| all W03 test modules explicitly | 87 | 3,678 | 0 |
| `NumStabilityTest.Reorganization.W03` | 1 aggregate | 3,679 | 0 |
| W05 canonical-only | 79 | 3,011 | 0 |
| W05 old-path-only | 10 | 2,935 | 0 |
| W05 focused Sylvester/Schur/inverse-bound | 3 | 2,899 | 0 |
| all W05 test modules explicitly | 92 | 3,034 | 0 |
| `NumStabilityTest.Reorganization.W05` | 1 aggregate | 3,035 | 0 |
| W05 retained W06 surface | 12 | 3,132 | 0 |
| `lake build NumStability NumStabilityTest` | 2 roots | 7,057 | 0 |
| `lake test` | full test target | 7,055 scheduled | 0 |
| official `lake build NumStability` during combined extraction | 1 root | 5,410 | 0 |

`lake test` prints no final job-summary line; it scheduled 7,055 jobs and the highest numbered progress line was 7,052/7,055 before its zero exit.

## Strict source and projection replay

Strict-source format-2 generation exited zero with zero import cycles and zero forbidden reusable-to-Source reachability. One full integrated format-2 candidate was used for both projection replays. Its raw TSV SHA-256 is `1DA19910927D41F4B45266ABA3F5E1A1F165637F7E984F8A19E15DA4FBB4A8D0`.

Before replay, the following frozen hashes were verified:

- checker: `29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443`
- C0004 combined baseline: `CCF7ACAE1D9306C03D79495B548E598C9A3132DC99A98C4212219A453CB27FA8`
- P0005 graph: `7B5A07528409CCCDC8B45F94B8F5FC977A2749601F8ED2D6B18D161CD27838B7`
- P0006 graph: `6A15BC343C895BCE66A92B09EC333300CA842BEC249DDF2DC723D0832098FFB5`

The exact recorded checker arguments were replayed with only the candidate placeholder replaced:

| Projection | Selected | Relocated | Signature edges | Body/proof edges | Union edges | Exit |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| P0005 / W03 | 1,034 | 806 | 8,056 | 11,608 | 11,932 | 0 |
| P0006 / W05 | 921 | 783 | 8,562 | 6,894 | 11,020 | 0 |

W03 preserves 228 retained declarations, including all 93 private declarations, across 16 declaration-bearing historical facades; its other 10 historical owners are pure import shims. W05 preserves its exact 138-declaration private reverse closure (3 private and 135 public declarations) in `Higham16`; its 783 relocations divide into 502 reusable and 281 source-numbered declarations.

## Official C0005 combined baseline

The official extractor ran from the clean checkpoint code commit under the same named mutex:

`python tools/architecture/generate_baseline.py --output-dir docs/architecture/phases/2026-08-repository-reorganization/baselines --name C0005-combined --keep-dependency-tsv benchmark-results/C0005-combined.tsv`

It completed 5,410 Lean jobs with exit zero and recorded `library_source_clean: true`, an empty dirty-path list, and exact commit `240c0d041781385a647fbec461d6863537e562cb`. The capture contains 1,859 modules, 3,028,763 source lines, 1,424,405 nonblank lines, 13,059 direct imports, 56,903 declarations, 266,387 signature edges, 382,872 body/proof edges, and 424,082 union edges.

- JSON SHA-256: `D961829AA197564A94193B9909695E6DA077D02B64F07EFC6FC531BB291EF190`
- Markdown SHA-256: `62EA29BDC4E881AB57D86E1B7A38369B2E38C0E904C67E937F1C0391EF966E09`
- Raw dependency TSV SHA-256: `1DA19910927D41F4B45266ABA3F5E1A1F165637F7E984F8A19E15DA4FBB4A8D0`
- Source-tree SHA-256: `F830DB03D2E532A74087FC2AF597A144B86FC3A7591D6F39FDB3D5AFEF64AE2E`

## Acceptance and retirement boundary

C0005 accepts M03 and M05 at the green code commit. M04, M06, and M08 become ready but are not activated. B0004 and B0005 are accepted with retirement due until the acceptance-control commit itself passes Lean CI. Only after that green control commit may the two exact remote delivery refs be deleted and their retirement recorded; local worktrees and local branches remain preserved.
