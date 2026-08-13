# C0002 acceptance evidence

Checkpoint code commit: `9d2334d77f1a38f8a4caa81fe53eeb11a8e3e7cd`

Accepted at: `2026-08-13T07:17:54Z`

## Exact green code run

[GitHub Lean CI run 31673501960](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31673501960)
completed successfully for the exact checkpoint code commit on the `main` push
event. The run was created at `2026-08-13T06:21:01Z` and completed at
`2026-08-13T06:59:37Z`. Job
[94362951630](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31673501960/job/94362951630)
ran from `06:21:05Z` through `06:59:37Z`. Its architecture and source-graph
step passed from `06:21:33Z` through `06:25:17Z`; its clean
`lake build NumStability NumStabilityTest` step passed from `06:25:17Z`
through `06:59:33Z`. The Lake sentinel reported
`Build completed successfully (9138 jobs)`.

## Immutable deliveries, scope, and true merges

R11 delivery `444a03259af510bdfe0921d1847b6add1b26ed73` and R12 delivery
`0726678a0f2db56e533f3b956a2f7f1531059d7d` are direct children of exact
C0001 code commit `117aa2bb7e61f41e1531a78452f9f7f6cd5b0771`. Their local and remote
branch tips matched those immutable reports before integration. Each delivery
is preserved by a separate true merge:

- merge `10169717ce4966e9963885b04e7b7733a3bc7730` has parents
  `de0ea2a54ea53d0e3724a72135d6da7d22739226` and exact R11 delivery
  `444a03259af510bdfe0921d1847b6add1b26ed73`;
- merge `1495047a1befb1431f0501cf7a423c8e77f8661a` has parents
  `10169717ce4966e9963885b04e7b7733a3bc7730` and exact R12 delivery
  `0726678a0f2db56e533f3b956a2f7f1531059d7d`.

Both deliveries and both merge commits are ancestors of the checkpoint code
commit. No squash, rebase, or cherry-pick was used. The exact post-R12
integration range
`1495047a1befb1431f0501cf7a423c8e77f8661a..9d2334d77f1a38f8a4caa81fe53eeb11a8e3e7cd`
contains exactly 146 modified paths and no additions, deletions, or renames.
The permanent `C0002-integrator-paths.tsv` ledger has 146 rows and SHA-256
`004B3B305708CB4C9098C931938F9C0385181B81FD22387632E347D667896A3A`.
It records the 133 reviewed-union paths and the bounded Chapter 19 aggregate,
compatibility-exception, control, DAG, validator, and documentation follow-ups.
No generated build artifact is tracked.

## Shared requests and reviewed union

R0003 and R0004 were independently generated from the same exact C0001
preimage. Their whole-file requests overlap only at `NumStabilityTest.lean`,
`docs/architecture/layout-exceptions.json`, and
`docs/architecture/tiers.json`. The integrator therefore applied the reviewed
same-preimage union exactly once after both true merges; sequential request
replacement was not used.

| Artifact | Paths | SHA-256 |
| --- | ---: | --- |
| R0003/R0004 union patch | 133 | `A6AB1307D19CBF2BEDDA37EAC8C68FFB405292B405E068908E6E4F15406A3E3B` |
| union postimage manifest | 133 | `7279EDF6AF7277C2A4DD45286AEE97878EBFD025A89B240A6A644EE6FB665701` |
| union review | 133 | `5B43D44B16496CAEACB14DE98FB4472B1698E18C3708B3BCD058C64C119F59DB` |

The reviewed forward tree is
`439514c9ebaf7fb9cd2420ed92121a55a04ab9fa`. The bounded follow-up makes
`NumStability.Source.Higham.Chapter19.Sensitivity` and
`NumStability.Source.Higham.Chapter19.StoredLoop` descendant-complete
aggregates. The compatibility checker records self-ratcheting exceptions for
exactly the two retained historical support imports in byte-identical
`NumStability.Source.Higham.Chapter19.Core`; the frozen Core content SHA-256 is
`8599A1F13F1A241EFE90BB1059D98C09A4419BE4C2202B97F45DEC69189B3FE3`.

## Static architecture gates

All repository-owned commands below exited zero against the integrated code
commit before the acceptance-control edits:

- `python -B tools/architecture/check_phase.py --self-test`;
- `python -B tools/architecture/check_phase_projection.py --self-test`;
- `python -B tools/architecture/check_completion_phase_projection.py --self-test`;
- `python -B tools/architecture/check_completion_phase.py --self-test`;
- `python -B tools/architecture/check_phase.py --all-phases`;
- `python -B tools/architecture/check_completion_phase.py`;
- `python -B tools/architecture/check_layout.py`;
- `python -B tools/architecture/check_compatibility.py` (384 forwarding
  modules, 868 canonical targets, and 2 exact retained-import exceptions);
- `python -B tools/architecture/check_provenance.py` (137 Apache-marked files
  and 5 evidenced upstream modules);
- `git diff --check` outside immutable patch payloads.

Layout reports 2,642 production modules, 2,365 classified modules (89.516%),
277 unclassified modules, 9 mixed modules, 13 missing module docstrings, 241
noncanonical names, 16 declaration-bearing umbrellas, and zero unsorted
aggregate imports. Tier counts are 1,046 source, 377 aggregate, 384
compatibility, 542 reusable, 2 internal, 5 upstream, and 9 mixed. It also
reports zero placeholders, top-level axioms/constants, tracked generated
artifacts, or test-reachability failures.

The strict-source extraction command
`python -B tools/architecture/generate_baseline.py --skip-declarations --strict-source --output-dir benchmark-results/C0002-strict-source --name source`
held the build mutex, exited zero in 23.085 seconds, and found zero unresolved
project imports, import cycles, reusable-to-Source paths, or forbidden
canonical-to-historical reachability. Its ignored JSON and Markdown hashes are
`66A2792F207549B48E1AF18A6495A64E6430BB4F070C8F4D52A7AE9627D9FFD3`
and `7924DE66523DA66DF0E9BDD0D3B32BE00850748506496BC2BBA830C1D7DEC05A`.

## Integrated projections

The official C0002 format-2 dependency TSV was generated from the exact code
tree under `Local\lean-reorganization-2026-08`. It contains 56,903
declarations and has SHA-256
`E03DB7A24886AD0B45C7371FE30ACE3AD135B3C4CC9866D65186753CD14FAD4C`.
Both frozen exact-C0001 projections were replayed against that one C0002
candidate by replacing only their literal candidate placeholder argument:

| Projection | Selected | Relocated | Signature | Body/proof | Union | Private map | Seconds | Exit |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| P0003 / R11 | 1,477 | 412 | 15,172 | 18,056 | 19,873 | 17 | 4.669 | 0 |
| P0004 / R12 | 34 | 34 | 80 | 133 | 139 | 0 | 4.194 | 0 |

Every relocated declaration and every signature/body edge was preserved. The
remaining 1,065 R11 declarations deliberately stay in the byte-identical
Chapter 19 Core outlier; its exact private normalization map remains frozen.

## Focused builds, full build, and tests

Every local Lean operation held Windows named mutex
`Local\lean-reorganization-2026-08`; checkpoint JSON normalizes the lock name
to `lean-reorganization-2026-08`. Exact module lists were ordinal-sorted and
hash-pinned.

| Gate | Modules | Module-list SHA-256 | Jobs | Seconds | Exit |
| --- | ---: | --- | ---: | ---: | ---: |
| canonical-only | 11 | `D771D9EDED55955D9AD84BD9E2C276DC5BBF00FE06E296E1C2194E8D94801F47` | 3,068 | 6.898 | 0 |
| semantic focused | 11 | `60A254F45D2FCEA21AE6A5E6D683C55ADFA011C5C38A23568B5D4CE137412FCA` | 3,068 | 9.366 | 0 |
| old-path-only | 68 | `2310514CE821C8A8A98C1E09D4A076AAE6C2C97FCE98D38CA60A8428472685C4` | 3,471 | 5.795 | 0 |
| protected consumers | 140 | `BF83EDF20D08EA78586335FA4326E201AE6621B7122F0166A741FCA550639F49` | 3,912 | 6.047 | 0 |
| R11/R12 aggregate roots | 2 | `B2268C70677A8D895BC09F50DADA5E141AD6A5EF9CF48BAC144256442D66D249` | 4,094 | 6.665 | 0 |

The local cached `lake build NumStability NumStabilityTest` completed 9,138
jobs in 11.377 seconds. The exact remote code run independently rebuilt both
roots from a clean checkout. `lake test` exited zero in 9.838 seconds.

## Official C0002 combined baseline

After the exact code CI was green, the official extractor ran from the clean
checkpoint code commit under the named mutex:

`python -B tools/architecture/generate_baseline.py --output-dir docs/architecture/phases/2026-08-repository-reorganization-completion/baselines --name C0002-combined --keep-dependency-tsv benchmark-results/C0002-combined.tsv`

The authoritative clean-tree run completed 6,143 jobs in 187.978 seconds. A
separate deterministic `--dependency-tsv ... --check` replay exited zero in
30.164 seconds. The baseline records exact commit
`9d2334d77f1a38f8a4caa81fe53eeb11a8e3e7cd`,
`library_source_clean: true`, and an empty dirty-path list. It contains 2,642
production modules, 4,001,883 source lines, 1,452,020 nonblank lines,
74,555,226 bytes, 27,407 direct imports (16,479 internal and 10,928 external),
56,903 declarations, 266,387 signature edges, 382,872 body/proof edges, and
424,082 union edges.

- JSON SHA-256: `0A062C8EB887E34907BF15F9423EDA6E7FB3DD032495B6DE98A7ED8538A32485`
- Markdown SHA-256: `0866C152BD9162719EBC3343A7B1B76BB8B6FBB647DCF5B3389BD7E18F6EC705`
- raw dependency TSV SHA-256: `E03DB7A24886AD0B45C7371FE30ACE3AD135B3C4CC9866D65186753CD14FAD4C`
- C0002 inventory SHA-256: `BB5AE8029CC3DC547BA1E4C8B581BA11948E527810AC29F0EBE8E1CC5D81BF02`
- C0002 integrator ledger SHA-256: `004B3B305708CB4C9098C931938F9C0385181B81FD22387632E347D667896A3A`

The inventory has 2,262 already-complete rows, 380 remaining in-scope rows,
and 356 distinct rows carrying residual architecture debt. M01, M02, M11,
and M12 are satisfied at C0002; no other milestone is claimed.

## Repository-wide final gates and successor decision

The repository is not complete. The exact final-gate audit is:

| Final gate | Status | Evidence |
| --- | --- | --- |
| architecture | PASS | phase, inventory, routes, projections, requests, ancestry, and validators pass |
| build profiles | PASS | canonical, focused, old, protected, aggregate, and full profiles pass |
| canonical layout | FAIL | 9 mixed, 241 noncanonical, and 16 declaration-bearing umbrella modules remain |
| classification complete | FAIL | 277 production modules remain unclassified |
| compatibility | PASS | 384 forwarding modules, 868 canonical targets, and two self-ratcheting exceptions pass |
| documentation current | PASS | checkpoint, phase, compatibility, and migration control documents are current at C0002 |
| entrypoint reachability | PASS | layout reports zero supported-entrypoint reachability failures |
| forbidden reachability zero | PASS | strict-source and protected-consumer checks report zero forbidden paths |
| full build | PASS | local and exact green remote full builds pass |
| full tests | PASS | focused matrices and `lake test` pass |
| generated artifacts absent | PASS | zero tracked generated artifacts |
| module documentation | FAIL | 13 production modules lack module docstrings |
| outlier review | PASS | graph-derived R11 review retained and content-pinned Chapter19.Core deliberately |
| provenance | PASS | 137 Apache-marked and 5 evidenced upstream modules pass |

Because three final-gate classes fail and 356 residual-debt rows remain,
bounded-phase and repository-wide completion stay `incomplete`. The frozen
milestone DAG makes M03/R03 and M07/R07 dependency-ready candidates after
C0002, but they are not an authorized pair. Any later wave requires a fresh
exact-C0002 inventory, graph, route, private-closure, shared-consumer, overlap,
operator-authority, and green planned-control review.

## Acceptance and retirement boundary

C0002 accepts M11 and M12 at the exact green code commit. B0003 and B0004
become accepted with retirement due; P0003 and P0004 become retired immutable
evidence; R0003 and R0004 become applied. The temporary `codex-local`
authorization on `claude-lane` expires and the eleven future R05/R09 owner
reservations are released; those paths require fresh C0002 preimages before
later activation. The exact remote delivery refs and worker worktrees remain
present until the acceptance-control commit itself passes Lean CI. Only then
may evidence be archived, refs be deleted with exact expected-tip leases, and
worktrees be removed without force in a separate retirement control.
