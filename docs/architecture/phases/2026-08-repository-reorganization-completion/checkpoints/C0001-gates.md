# C0001 acceptance evidence

Checkpoint code commit: `117aa2bb7e61f41e1531a78452f9f7f6cd5b0771`

Accepted at: `2026-08-11T22:14:28Z`

## Exact green code run

[GitHub Lean CI run 31539572494](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31539572494)
completed successfully for the exact checkpoint code commit on the `main` push
event. The run was created at `2026-08-11T21:48:12Z` and completed at
`2026-08-11T22:00:05Z`. Job
[93938660639](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31539572494/job/93938660639)
ran from `21:48:21Z` through `22:00:04Z`. Its architecture and source-graph
step passed from `21:48:46Z` through `21:52:26Z`; its clean
`lake build NumStability NumStabilityTest` step passed from `21:52:26Z`
through `22:00:02Z`. The Lake sentinel reported
`Build completed successfully (8895 jobs)`.

## Immutable deliveries, scope, and true merges

R01 delivery `0bdf03a383377c8c6da89d85393e56fca8c00ccd` and R02 delivery
`f790c8413412177bb74f47fee74bb12c48c11155` are direct children of exact
C0000 code commit `b1b18772d80185ec08f49c818919558645c330a1`. Their remote branch
tips matched those reports before integration. Each delivery is preserved by a
separate true merge:

- merge `b5966cdc88d136936e6566010cd4113b81f20711` has parents
  `f98f0c8598b7834cb9a80567bc57053e9befa66a` and exact R01 delivery
  `0bdf03a383377c8c6da89d85393e56fca8c00ccd`;
- merge `52632d28f0c78438d883bde337700f330895159a` has parents
  `b5966cdc88d136936e6566010cd4113b81f20711` and exact R02 delivery
  `f790c8413412177bb74f47fee74bb12c48c11155`.

Both deliveries and both merge commits are ancestors of the checkpoint code
commit. No squash, rebase, or cherry-pick was used.

The independent R01 audit found exactly 98 changed paths: 16 modified owners
and 82 additions below authorized destination/evidence prefixes, with zero
unauthorized, forbidden, shared, deleted, renamed, or casefold-colliding paths.
The independent R02 audit found exactly 145 changed paths: 28 modified owners,
14 production destinations, 63 tests, and 40 delivery/evidence paths, again
with zero unauthorized, forbidden, shared, deleted, or renamed paths. R02's
worker-authored ledger incorrectly claimed 113 paths and omitted 32 authorized
delivery-tree artifacts. The primary-human corrected ledger
`reviews/R02-intake-scope.tsv` has SHA-256
`801759184E6F986D009F84E84164FD1DA06FA2B3BFC1BDD30A2982FD509132E0`;
the audit has SHA-256
`B6309C9F54CF025CFD30D8F84F420B6F65D178318FB45AB05F073AFAA9E992AE`.

The exact post-merge integration range
`52632d28f0c78438d883bde337700f330895159a..117aa2bb7e61f41e1531a78452f9f7f6cd5b0771`
contains 30 paths. Its permanent ledger is `C0001-integrator-paths.tsv`,
SHA-256 `2A1735AD3DF02CCD596787D7170B7D7B365A9EDA123B6C942B152127570B57F7`.
The separate pre-merge `.gitattributes` normalization commit
`f98f0c8598b7834cb9a80567bc57053e9befa66a` preserves LF bytes for formal
patches. No generated build artifact is tracked.

## Shared requests and reviewed unions

R0001, R0002, and supplemental primary-human R0002T were independently
replayed from the same exact C0000 tree
`3795e530fa6352ef1237be6361909a030cfb6f29`. Every patch touched exactly its
recorded paths, applied cleanly, matched its hash-pinned postimages, and
reversed to the exact C0000 tree.

| Request | Paths | Bytes | Patch SHA-256 | Forward tree |
| --- | ---: | ---: | --- | --- |
| R0001 | 5 | 7,033 | `E5A8F2C07CFE899B3F6B9C486989A92FF94CE99E16EF104278D52BADD0B8FA8C` | `06b632877c3f901c655ce657e3e157e8dc1ec1fa` |
| R0002 | 7 | 12,922 | `53CFC3ACAC6C3C49D708E97688B8206530860C91CB70A190CE7DC6E4C819835D` | `ac8c9ec8b15c2c8de45448a99bed3c6195c69d0a` |
| R0002T | 2 | 7,789 | `93EE50B01F5D517C813B82BE5A0B8885DFBE981FB1029EB5AD634A9875DB83F9` | `3bf417dff8d00aac09f35fb53cc82c41ea1fe221` |
| reviewed R0001/R0002 union | 11 | 19,514 | `E73A8D881DD51CCE710CCB1B4C30320DFE0E6B666F6FC8C0A3E9C167588957E6` | `479bceb73c6e635a8af2422721081db02f7da3d0` |

R0001 and R0002 overlap only at `NumStability/Algorithms.lean`. The reviewed
union manifest has SHA-256
`67AFB0F6FBADBB33B5755E9300972A7F4431EB22330F1366D1165EFBCC3FB163`
and its review has SHA-256
`620CFDEFA27F49655D0F399A56461DD60B7D8BCB2169BF1E2C84B515A46F7DF5`.
It was applied once after both merges; sequential whole-file replacement was
not used. R0002T records the two R02 test-root paths omitted from the worker's
formal request. The integrated R01-routine/R0002T test-root union is reviewed
at SHA-256
`B223E12C8B9571A41488F6ED0A3A180B2AA91C3870774081CE66073B7EBEB487`.

## Static architecture gates

All commands below exited zero against the integrated code commit:

- `python -B tools/architecture/check_phase.py --self-test`;
- `python -B tools/architecture/check_phase_projection.py --self-test`;
- `python -B tools/architecture/check_completion_phase_projection.py --self-test`;
- `python -B tools/architecture/check_completion_phase.py --self-test`;
- `python -B tools/architecture/check_phase.py --all-phases`;
- `python -B tools/architecture/check_completion_phase.py`;
- `python -B tools/architecture/check_layout.py` (135.9 seconds);
- `python -B tools/architecture/check_compatibility.py` (381 forwarding
  modules and 865 canonical targets);
- `python -B tools/architecture/check_provenance.py` (137 Apache-marked files
  and 5 evidenced upstream modules);
- `git diff --check` outside immutable patch payloads.

Layout reports 2,631 production modules, 277 unclassified modules, 9 mixed
modules, 72 missing module docstrings, 244 noncanonical names, 21
declaration-bearing umbrellas, and zero unsorted aggregate imports. It also
reports zero placeholders, top-level axioms/constants, tracked generated
artifacts, or test-reachability failures. All 34 R01/R02 destination modules
are reachable through supported entrypoints. The R01 and R02 test aggregates
contain exactly 41 and 63 sorted, unique, declaration-free test imports.

The strict-source extraction command
`python -B tools/architecture/generate_baseline.py --skip-declarations --strict-source --output-dir benchmark-results/C0001-strict-source --name source`
held the build mutex, exited zero in 17.725 seconds, and found zero unresolved
project imports, import cycles, reusable-to-Source paths, or forbidden
canonical-to-historical reachability. Its ignored JSON and Markdown hashes are
`873F3CFEB6AC33292092D1FEE83F0326A4B26322CD0F9133889F22AF75D246B1`
and `B61B7A1099840FA642816A820A865E8153F6486B87D6EE414288C4C3EF85F226`.

## Integrated projections

One format-2 candidate was generated from the integrated code tree while
holding `Local\lean-reorganization-2026-08`. It completed 6,133 Lean jobs in
401.728 seconds, scanned 56,903 declarations and 649,259 typed dependency
rows, and has raw TSV SHA-256
`55E0D29D626D746CB165DD7C874DA11A96B72602A66C1A6D8173F986178536C4`.
Both projection records were replayed against that exact same file, changing
only their literal candidate placeholder arguments:

| Projection | Selected | Relocated | Signature | Body/proof | Union | Private map | Seconds | Exit |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| P0001 / R01 | 243 | 243 | 693 | 1,341 | 1,422 | 10 | 3.290 | 0 |
| P0002 / R02 | 142 | 142 | 460 | 945 | 966 | 76 | 3.234 | 0 |

Every selected declaration relocated and every signature/body edge was
preserved. The private normalization maps remained exact and no reusable
destination reaches `NumStability.Source`.

## Focused builds, full build, and tests

Every local Lean operation held Windows named mutex
`Local\lean-reorganization-2026-08`; checkpoint JSON normalizes the lock name
to `lean-reorganization-2026-08`. The exact invoked module lists were
ordinal-sorted and hash-pinned.

| Gate | Modules | Module-list SHA-256 | Jobs | Seconds | Exit |
| --- | ---: | --- | ---: | ---: | ---: |
| canonical-only | 34 | `E1A273A16C65EA1906701CF085AF319103341A916B78C694177FE59E9D0E07D2` | 3,588 | 5.010 | 0 |
| semantic focused | 19 | `4BD592853F688AE7BC69F952D024B49B7A4314B16CC200484C9054A9CD767CCB` | 6,033 | 6.322 | 0 |
| old-path-only | 44 | `019BB29BE341B7A60E75E3A9DA798D35494EC2AC47A00E2F4BE918E7DE052270` | 3,756 | 4.908 | 0 |
| protected consumers | 7 | `6C64FDF572584A6DD005A4E226B24F8B61A55F061A3719D3B2E0BACF31BB9FA3` | 5,800 | 6.245 | 0 |
| R01/R02 aggregate roots | 2 | `C04361F7CC214BEB87C64D300CCA546040C798D53291415FB91A3360A6B3FCB8` | 6,164 | 6.425 | 0 |

The first integrated `lake build NumStability NumStabilityTest` completed in
296.4 seconds; its exact cached verification completed 8,895 jobs in 9.946
seconds. The exact remote code run independently rebuilt both roots from a
clean checkout. `lake test` exited zero, with the final cached verification
completing in 7.851 seconds.

## Official C0001 combined baseline

After the exact code CI was green, the official extractor ran from the clean
checkpoint code commit under the named mutex:

`python -B tools/architecture/generate_baseline.py --output-dir docs/architecture/phases/2026-08-repository-reorganization-completion/baselines --name C0001-combined --keep-dependency-tsv benchmark-results/C0001-combined.tsv`

The authoritative clean-tree run completed 6,133 jobs in 140.125 seconds. A
separate deterministic `--dependency-tsv ... --check` replay exited zero in
24.022 seconds. The baseline records exact commit
`117aa2bb7e61f41e1531a78452f9f7f6cd5b0771`,
`library_source_clean: true`, and an empty dirty-path list. It contains 2,631
production modules, 4,000,250 source lines, 1,450,782 nonblank lines,
74,497,180 bytes, 27,338 direct imports (16,452 internal and 10,886 external),
56,903 declarations, 266,387 signature edges, 382,872 body/proof edges, and
424,082 union edges.

- JSON SHA-256: `F6AD7BC1267CB73968D8933D1126DCE30AD2748E1B2EFD611C3D6509872243F2`
- Markdown SHA-256: `B7B5937966FED085E922490DCD492A5183017A0A373457141D3F65D313F5A6C6`
- raw dependency TSV SHA-256: `55E0D29D626D746CB165DD7C874DA11A96B72602A66C1A6D8173F986178536C4`
- source-tree SHA-256: `8CC24FE4509CEA7C8494372EFECD8AF7DA37721BCE9A5D8C0EEDC6A17FFFBC3D`
- C0001 inventory SHA-256: `E07B4BA74EE62737B8B2AB8DDF8FA9E43C8614DFFDC26C5E69535A4E38F1F57F`
- C0001 integrator ledger SHA-256: `2A1735AD3DF02CCD596787D7170B7D7B365A9EDA123B6C942B152127570B57F7`

The inventory has 2,183 already-complete rows, 448 remaining in-scope rows,
and 423 distinct rows carrying residual architecture debt. M01 and M02 are
satisfied at C0001; no other milestone is claimed.

## Repository-wide final gates and successor decision

The repository is not complete. The exact final-gate audit is:

| Final gate | Status | Evidence |
| --- | --- | --- |
| architecture | PASS | phase, scope, routes, projections, requests, ancestry, and validators pass |
| build profiles | PASS | canonical, focused, old, protected, aggregate, and full profiles pass |
| canonical layout | FAIL | 9 mixed, 244 noncanonical, and 21 declaration-bearing umbrella modules remain |
| classification complete | FAIL | 277 production modules remain unclassified |
| compatibility | PASS | 381 forwarding modules and 865 canonical targets pass |
| documentation current | PASS | checkpoint, phase, compatibility, and migration control documents are current at C0001 |
| entrypoint reachability | PASS | layout reports zero supported-entrypoint reachability failures |
| forbidden reachability zero | PASS | strict-source and protected-consumer checks report zero forbidden paths |
| full build | PASS | local and exact green remote full builds pass |
| full tests | PASS | focused matrices and `lake test` pass |
| generated artifacts absent | PASS | zero tracked generated artifacts |
| module documentation | FAIL | 72 production modules lack module docstrings |
| outlier review | FAIL | the Chapter 19 Core residual still requires its graph-derived R11 review |
| provenance | PASS | 137 Apache-marked and 5 evidenced upstream modules pass |

Because four final gates fail and 423 residual-debt rows remain, bounded-phase
and repository-wide completion stay `incomplete`. A fresh C0001 graph review
selects R11 (QR/Chapter 19 residual) and R12 (Chapter 13 source residual) as
the only currently ready pair with zero owner, destination, import,
reachability, signature, body, and shared-consumer overlap. Their controls are
planned only after C0001 acceptance and retirement become durable.

## Acceptance and retirement boundary

C0001 accepts M01 and M02 at the exact green code commit. B0001 and B0002
become accepted with retirement due; P0001 and P0002 become retired immutable
evidence; R0001, R0002, and R0002T become applied. The exact remote delivery
refs and worker worktrees remain present until the acceptance-control commit
itself passes Lean CI. Only then may evidence be archived, refs be deleted
with exact expected-tip leases, and worktrees be removed without force in a
separate retirement control.
