# C0008 acceptance evidence

Checkpoint code commit: `b1b18772d80185ec08f49c818919558645c330a1`

Accepted at: `2026-08-11T07:00:00Z`

## Remote gate

[GitHub Lean CI run 31463301557](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31463301557)
completed successfully for the exact checkpoint code commit on the `main` push
event. The run was created at `2026-08-11T05:56:04Z` and completed at
`2026-08-11T06:53:12Z`; job 93691004160 ran from `05:56:07Z` through
`06:53:11Z`. Its architecture, phase-contract, layout, compatibility,
provenance, and strict-source step passed from `05:56:33Z` through
`06:00:06Z`. Its clean `lake build NumStability NumStabilityTest` step passed
from `06:00:06Z` through `06:53:10Z`; the Lake sentinel reported
`Build completed successfully (8750 jobs)`.

## Delivery ancestry and scope

W07 delivery `176c72838828795b89f4aa822479010c7860c8e5` and corrected W10
delivery `9e7604cbdbd2314bc4bf38bcd9e342c3accfb1d6` both descend from exact
C0007 code commit `9eb534a06db267203c2b9b88227edd44fc64f5db`. They are ancestors
of the checkpoint code commit through separate true Git merges
`9399c0531c6c6431e3f8def33fae1df3fbb060a6` and
`25ea10390ab118dbfc3ecf2c05ba9e33fbe1e626`.

The immutable W07 scope audit contains 103 paths: 98 added and 5 modified,
including all 5 historical owners. W10 contains 274 paths: 247 added and 27
modified, including all 27 historical owners. Each audit covers every owned
path and authorized destination with zero forbidden or unowned paths. The
waves have zero owner overlap and zero production-destination overlap. Relative
to C0007, W07 contributes 34 production modules (9 reusable and 25 source),
W10 contributes 96 (49 reusable and 47 source), and the integrator contributes
7 discovery aggregates.

The exact post-merge integration diff
`25ea10390ab118dbfc3ecf2c05ba9e33fbe1e626..b1b18772d80185ec08f49c818919558645c330a1`
contains 31 paths: 7 added aggregates, 6 added request artifacts, 2
added test aggregates, 6 modified aggregates, 2 modified classification files,
and 8 modified control files. Status totals are 15 added and 16 modified. The
permanent path ledger is `C0008-integrator-paths.tsv`, SHA-256
`32A5F24B774E8275A69BAEF4F1854A4ECD4E958BAA62380CA7050FDA160E3239`.
No generated build artifact is tracked.

## Shared integration requests and overlap changes

R0010 and R0011 were independently based on exact C0007 code commit
`9eb534a06db267203c2b9b88227edd44fc64f5db`. Their sorted patches, exact
preimages, and hash-pinned overlap reviews were independently replayed in
disposable C0007 indexes. Each patch applied to exactly its recorded path set
and reversing it restored C0007 tree
`91ea7ded609393125387f5a575936993c1cb0e5e`. The forward R0010 index tree is
`45141e1cfe7e777b6e3e678de92dfc888439ae04` with 6 paths; the forward R0011
index tree is `704f458614b352f10389bcf1c7319fe43af0755c` with 13 paths.

- R0010 / W07: 6 paths, 187,896 bytes; patch SHA-256
  `E05687DC8959C8B3B24DE30E996553A780839CB2C501D5A0BBBF6A39B40BF425`;
  review SHA-256
  `8D8BF1D34FFF61444CC66CAB66BFFCB5E6BF9D55A31453EC32349CED5B5A6B18`.
- R0011 / W10: 13 paths, 33,353 bytes, 25 zero-context hunks; patch SHA-256
  `71D9BD0B68C82848DAD3EBA4260A3F81FC4EF302524A68D14A449332BDA97F7A`;
  review SHA-256
  `BFA2C7D38F12AE7D95EEE6755A7CC7ED0D15FB43ED4033B314F4BD2204DEA740`.

Their only formal overlaps are `NumStabilityTest.lean`, `tiers.json`, and
`layout-exceptions.json`; the integrated postimages are the reviewed unions.
The accepted W06 destination
`NumStability/Algorithms/NormEstimation/OneNorm/All.lean` is deliberately
outside formal R0011 and matches the separately reviewed W06/W10 worker
postimage, blob `fd1f940d0dba70a19a8c207baeeee35305413433`. The integrated tier
manifest contains exactly 1,417 exact entries and 24 prefixes. The test root
adds exactly the W07 and W10 aggregates, and removing import commands from
every modified existing Lean file leaves its non-import text unchanged.

## Static and architecture gates

All commands below exited zero against the integrated code tree:

- `python -B tools/architecture/check_phase.py --self-test` and
  `python -B tools/architecture/check_phase_projection.py --self-test` passed
  all positive fixtures and rejected their negative drift fixtures.
- `python -B tools/architecture/check_phase.py` passed the delivered/request
  state before checkpoint publication: 8 checkpoints, 13 milestones, 12
  branches, 11 shared requests, and 13 baseline projections.
- `python -B tools/architecture/check_layout.py` reported 2,593 production
  modules; 277 unclassified, 45 mixed, 72 missing module docstrings, 268
  noncanonical names, 27 declaration-bearing umbrellas, and zero unsorted
  aggregates.
- `python -B tools/architecture/check_compatibility.py` reported 337 forwarding
  modules and 685 canonical targets.
- `python -B tools/architecture/check_provenance.py` reported 137 Apache-marked
  production files and 5 evidenced upstream modules.
- The placeholder/axiom and generated-artifact audits found zero `sorry`,
  `admit`, top-level `axiom`, or top-level `constant` commands and zero tracked
  generated or private-skill artifacts.
- W07 and W10 static scope, route, private-retention, and import-graph audits
  passed. The combined graph has zero unresolved project imports, zero cyclic
  components, zero reusable-to-Source edges or reachability, and zero
  canonical-to-historical reachability.
- `git diff --check` passed for every non-patch path. The sole diagnostic was
  the already hash-frozen R0010 patch's intentional `+ ` line at patch line
  57; it was preserved byte-for-byte. CRLF notices were informational only.

## Integrated Lean builds and tests

Every local Lean operation held Windows named mutex
`Local\lean-reorganization-2026-08`; checkpoint JSON normalizes the lock name
to `lean-reorganization-2026-08`. The exact module sets were ordinal-sorted,
mutually disjoint, and hash-pinned before invocation.

| Gate | Exact modules | Module-list SHA-256 | Jobs | Seconds | Exit |
| --- | ---: | --- | ---: | ---: | ---: |
| canonical-only | 130 | `9B789AA5B8A52C648590FFFB638D07BC4B6D971E5F8F75ABDF76124636993FF6` | 3,749 | 8.200 | 0 |
| old-path-only | 32 | `71984EA7E1660EB87B85F0C934700F5130890A70E635FB3FB17B0E7BF196AA85` | 3,681 | 6.866 | 0 |
| semantic focused | 15 | `321A0B6E76EACFC05E4F9D741520EA275E2E7131E1BBC929C942717FE15F5390` | 3,661 | 4.855 | 0 |
| protected W06/W09 | 3 | `2D1595B948B80D58276E2CD1992DF36CFC1D6B347E19B42937911722276C05C8` | 3,544 | 5.532 | 0 |
| accepted consumers | 3 | `570C17EE02C9E76C36C3A34755B6035D8E2D3A90A8FC2FA55E0D396734E1A9A8` | 3,430 | 4.593 | 0 |
| W07/W10 aggregate roots | 2 | `C92C88652805485B6C34F48C6795FE4EA2A3633B2858235DE1CBE5C5CF69868A` | 3,863 | 4.927 | 0 |
| `lake build NumStability NumStabilityTest` | 2 roots | n/a | 8,750 | 8,424.988 | 0 |
| `lake test` | full test target | n/a | n/a | 75.162 | 0 |

The union of the two immutable delivery matrices contains 183 leaf tests with
SHA-256
`7B7FE42448DD2AB563A78497A6B71561C73DA7CEA5A92325FF3DC738DD369428`.
The remote gate independently rebuilt both full roots from a clean checkout.

## Strict source and projection replay

Combined strict-source generation ran under the mutex and exited zero in
18.396 seconds. It scanned all 2,593 production modules, classified 2,316, and
reported zero unresolved imports, cycles, and reusable-to-Source paths. The
separate W07/W10 static import audits reported zero canonical-to-historical
paths. The ignored strict-source JSON and Markdown evidence have SHA-256
`F88B2442FE4700C3D9DF0FF5944A4FE7216ED703917A6FB4D94AEA1F292AC03D`
and
`A7AF895C11E96BD94C55F8619848F3CE32AC7C513F5D4C5825699A85F0C776C1`.

The final precommit format-2 candidate was generated from the exact integrated
tree under the same mutex in 137.340 seconds. It scanned 56,903 declarations
and 649,259 typed dependency rows; its TSV SHA-256 is
`7973041136A13FEEBACA1C462868A9C9A3DB907FC7D8BC841601E14B3853F1C8`.
The exact recorded checker arguments were replayed with only the candidate
placeholder replaced:

| Projection | Arguments | Selected | Relocated | Retained | Signature | Body/proof | Union | Seconds | Exit |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| P0012 / W07 | 42 | 252 | 136 | 116 | 800 | 1,400 | 1,474 | 3.093 | 0 |
| P0013 / W10 | 73 | 1,029 | 895 | 134 | 2,394 | 4,844 | 5,075 | 3.337 | 0 |

Both replays scanned the same 56,903 declarations and 649,259 typed rows. W07
retains its exact 116-declaration private reverse closure. W10 retains 134
declarations: its 132-declaration private reverse closure plus two reviewed
re-entry declarations. No reusable destination depends on `Source`.

## Official C0008 combined baseline

The official extractor ran from the clean checkpoint code commit under the
same named mutex:

`python tools/architecture/generate_baseline.py --output-dir docs/architecture/phases/2026-08-repository-reorganization/baselines --name C0008-combined --keep-dependency-tsv benchmark-results/C0008-combined.tsv`

It completed 6,139 Lean extraction jobs and deterministic graph validation
with exit zero in 134.967 seconds. A separate deterministic
`--dependency-tsv ... --check` replay also exited zero. The baseline records
`library_source_clean: true`, an empty dirty-path list, format version 2, and exact commit
`b1b18772d80185ec08f49c818919558645c330a1`. It contains 2,593 production
modules, 4,001,811 source lines, 1,450,083 nonblank lines, 74,452,766 bytes,
26,833 direct imports (16,089 internal and 10,744 external), 56,903
declarations, 266,387 signature edges, 382,872 body/proof edges, and 424,082
union edges.

- JSON SHA-256: `2EA9D8C24D3E4D3EEA6B3A135FE195946BB8659C7E5FBF9452DADD89D1726A2F`
- Markdown SHA-256: `4A5B66823D07FBDAE0AD15F3C182035BCBF75F98D58F2856F05E80905AA6F9C6`
- Raw dependency TSV SHA-256: `7973041136A13FEEBACA1C462868A9C9A3DB907FC7D8BC841601E14B3853F1C8`
- Source-tree SHA-256: `AA47B4AAA1C0B04C1B1F1A1297701656B43283E5180B9CCC21922627EAEFD8D9`
- C0008 inventory SHA-256: `570868866D0FC81A6D051A8340E47364CFA761F22194A89CA60687AB1E1FCEFF`
- C0008 integrator-path ledger SHA-256: `32A5F24B774E8275A69BAEF4F1854A4ECD4E958BAA62380CA7050FDA160E3239`

## Acceptance and retirement boundary

C0008 accepts M07 and M10 at the green code commit. M90 becomes ready but
remains unactivated; bounded-phase and repository-wide completion remain
incomplete. C0007 remains the historical parent and C0008 becomes current.
B0011 and B0012 become accepted with retirement due; P0012 and P0013 become
retired immutable evidence; R0010 and R0011 become applied.

The two exact remote delivery refs and the clean named W07 delivery worktree
remain present until the C0008 acceptance-control commit itself passes Lean CI.
Only after that green control commit may the refs be deleted with exact-SHA
leases, the ignored W07 delivery artifacts be archived, and the clean W07
worktree be removed without force in a separate retirement step. Local worker
branches remain preservation targets. The clean
`C:\Users\qed_s\w10-worker` checkout is an integrator recovery/correction
checkout, not a worker-lane checkout or retirement target, and remains
preserved.
