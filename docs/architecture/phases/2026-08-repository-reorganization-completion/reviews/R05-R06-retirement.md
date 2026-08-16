# R05/R06 retirement and artifact archive

This primary-human review records the terminal retirement boundary for
B0006/R05 and B0007/R06. The accepted C0004 code checkpoint is
`783ae9a4951407ece046adb8631d5a8ff1795a18`; its acceptance-control commit is
`131a0c6f333de0eb47a67698decf36ee82e01dab`, whose sole parent is that exact
checkpoint code commit. The acceptance-control commit passed GitHub Lean CI
run
[31966141900](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31966141900),
build job
[95211495907](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31966141900/job/95211495907),
before retirement. The run was created at `2026-08-16T18:57:50Z` and completed
at `2026-08-16T19:06:41Z`; the job ran from `2026-08-16T18:57:53Z` through
`2026-08-16T19:06:41Z`. Its architecture and source-graph step passed from
`18:58:24Z` through `19:02:17Z`, and its library and smoke-test build passed
from `19:02:17Z` through `19:06:37Z`.

Both immutable deliveries remain ancestors of accepted C0004. R05 delivery
`26e89100b3c7c8a64a41426d517cbd563a40db72` enters the mainline through true
merge `538c7d248a0ccaec407a082ecb73b92d7c3faec2`; R06 delivery
`bfaf2ae917ed79165caa6cc58b3782984aa8d3d9` enters through true merge
`deee8e7ea0aeac7cfbd9fc2582eaf1f5b841fd0c`. Integration commit
`783ae9a4951407ece046adb8631d5a8ff1795a18` is the direct child of the R06
merge. B0006 and B0007 were retired together by `primary-human` at
`2026-08-16T19:08:57Z` against ancestry checkpoint C0004. Their immutable
delivery, integration, request, projection, and amendment evidence remain
unchanged.

## Remote refs and worktrees

The two remote delivery refs were deleted atomically using exact expected-tip
leases and were then verified absent:

| Branch | Remote ref | Expected immutable tip | Post-delete result |
| --- | --- | --- | --- |
| B0006/R05 | `refs/heads/codex/reorg-completion-2026-08-r05-least-squares-underdetermined-ch20-ch21` | `26e89100b3c7c8a64a41426d517cbd563a40db72` | absent from `git ls-remote --heads origin` |
| B0007/R06 | `refs/heads/codex/reorg-completion-2026-08-r06-schur-sylvester-pivoting-ch09-ch11-ch16` | `bfaf2ae917ed79165caa6cc58b3782984aa8d3d9` | absent from `git ls-remote --heads origin` |

Before cleanup, both named worker worktrees had exact HEADs equal to their
immutable delivery tips and no tracked, staged, unstaged, or ordinary
untracked changes. R05 material ignored evidence was archived and
hash-verified first. R06 had no material ignored evidence to archive. Both
worktrees were then removed with `git worktree remove` without `--force`:

| Wave | Removed worktree | Verified pre-removal HEAD |
| --- | --- | --- |
| R05 | `C:\Users\qed_s\higham-worktrees\completion-r05-claude` | `26e89100b3c7c8a64a41426d517cbd563a40db72` |
| R06 | `C:\Users\qed_s\higham-worktrees\completion-r06-codex` | `bfaf2ae917ed79165caa6cc58b3782984aa8d3d9` |

Both named paths and both Git worktree registrations are absent, with no
residual cache directory or other worktree residue. The local delivery branch
refs remain preserved at the exact immutable tips, so either remote ref can be
restored if required.

## Archived ignored evidence

The archive root is
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0004-R05-R06-20260816`.
All paths below are relative to that root. Byte counts and SHA-256 values were
recomputed from the archived files after copying and before worktree removal.

| Relative path | Bytes | SHA-256 |
| --- | ---: | --- |
| `R05/benchmark-results/R05-candidate.json` | 101,468 | `80A801572B2127CA0FD5402F8A8952CBB9C2FF71D8DEC77D7B5F3DC053160675` |
| `R05/benchmark-results/R05-candidate.md` | 20,698 | `007694C6D627D9271F74C591BAE2D9957438ABF41F52A031FDF43BC3E3136C84` |
| `R05/benchmark-results/R05-candidate.tsv` | 117,106,938 | `8DCA5AED79265D3D5055E46594BD4B9E55D0806E8143CB9D9AD46FAD0BFA35BC` |
| `R05/benchmark-results/R05-strict-source/source.json` | 88,466 | `856E264290687E634A31FED193C0641538F313697C25AB15DE104C57468554BD` |
| `R05/benchmark-results/R05-strict-source/source.md` | 9,491 | `856D9C8825049A326CBDF46C2D456DEE539F7FF81D38F1735A3DD87437AB4A9C` |

The five material files total 117,327,061 bytes. R06 had no material ignored
artifact, so the archive contains no R06 evidence row. The protected R0008
custody evidence at `C:\Users\qed_s\AppData\Local\Temp\r0008-shadow` and
`C:\Users\qed_s\r0008-package` remains present and untouched; the tracked
R0008 approval, review, patch, and postimage artifacts likewise remain
unchanged. C0004 remains the current checkpoint, and this retirement does not
create, authorize, plan, or activate a successor wave.
