# R11/R12 retirement and artifact archive

This primary-human review records the retirement boundary for B0003/R11 and
B0004/R12. The accepted C0002 code checkpoint is
`9d2334d77f1a38f8a4caa81fe53eeb11a8e3e7cd`; its acceptance-control commit is
`c92c48a348a0e09e7d6ac9d4ff1db7673a027648`. That exact acceptance-control
commit passed GitHub Lean CI run
[31678412178](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31678412178),
build job
[94378054384](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31678412178/job/94378054384),
before retirement. The run and job both concluded `success`; the job ran from
`2026-08-13T07:35:47Z` through `2026-08-13T07:42:49Z`. Its architecture and
source-graph step passed from `07:36:15Z` through `07:39:56Z`, and its library
and smoke-test build passed from `07:39:56Z` through `07:42:46Z`.

Both deliveries remain ancestors of the accepted C0002 code checkpoint through
their separate true merges: R11 delivery
`444a03259af510bdfe0921d1847b6add1b26ed73` through merge
`10169717ce4966e9963885b04e7b7733a3bc7730`, and R12 delivery
`0726678a0f2db56e533f3b956a2f7f1531059d7d` through merge
`1495047a1befb1431f0501cf7a423c8e77f8661a`. B0003 and B0004 were retired
together by `primary-human` at `2026-08-13T07:46:11Z` against ancestry
checkpoint C0002. Their immutable delivery and integration records remain
unchanged.

## Remote refs and worktrees

The two remote delivery refs were deleted atomically using exact expected-tip
leases:

| Branch | Remote ref | Expected immutable tip | Post-delete result |
| --- | --- | --- | --- |
| B0003/R11 | `refs/heads/codex/reorg-completion-2026-08-r11-qr-ch19` | `444a03259af510bdfe0921d1847b6add1b26ed73` | absent from `git ls-remote --heads origin` |
| B0004/R12 | `refs/heads/codex/reorg-completion-2026-08-r12-ch13-equations-table` | `0726678a0f2db56e533f3b956a2f7f1531059d7d` | absent from `git ls-remote --heads origin` |

Before cleanup, the named worker worktrees had empty tracked and untracked
status and exact HEADs equal to their immutable delivery tips. Material ignored
delivery evidence was archived and hash-verified first. Both worktrees were
then removed with `git worktree remove` without `--force`:

| Wave | Removed worktree | Verified pre-removal HEAD |
| --- | --- | --- |
| R11 | `C:\Users\qed_s\higham-worktrees\completion-r11-claude` | `444a03259af510bdfe0921d1847b6add1b26ed73` |
| R12 | `C:\Users\qed_s\higham-worktrees\completion-r12-codex` | `0726678a0f2db56e533f3b956a2f7f1531059d7d` |

After Git removed both registrations and all tracked/evidence content, Windows
left only a disposable `.lake` cache in each named directory. Those two exact
single-entry residues were verified and recoverably relocated below the archive
root at `disposable-worktree-residue/`; both original named worktree paths are
absent. The cache residues are not checkpoint evidence and are excluded from
the material-evidence manifest below. The local branch refs remain preserved at
the exact immutable delivery tips, so either remote ref can be restored if
required.

## Archived ignored evidence

The archive root is
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0002-R11-R12-20260813`.
All paths below are relative to that root. Byte counts and SHA-256 values were
recomputed from the archived files after copying and before worktree removal.

| Relative path | Bytes | SHA-256 |
| --- | ---: | --- |
| `R11/benchmark-results/R11-candidate.json` | 99,619 | `7338A9B8E63654064D8603EACC14D5B3FA84992B3B48EDE7F66EE1CB9E243C25` |
| `R11/benchmark-results/R11-candidate.md` | 20,236 | `D364905DC25D8F27AB8E8FD498C1BAAAAE3FF8C2D00219C477170D3797D00060` |
| `R11/benchmark-results/R11-candidate.tsv` | 116,736,010 | `FBF9B388DF9107D99A64B5427066C38E6325ACFC788731207A14E546D090C3F9` |
| `R11/benchmark-results/R11-strict-source/R11-worker-strict-source.json` | 99,619 | `7338A9B8E63654064D8603EACC14D5B3FA84992B3B48EDE7F66EE1CB9E243C25` |
| `R11/benchmark-results/R11-strict-source/R11-worker-strict-source.md` | 20,236 | `D364905DC25D8F27AB8E8FD498C1BAAAAE3FF8C2D00219C477170D3797D00060` |
| `R12/benchmark-results/R12-candidate.json` | 99,488 | `EEB68C5AD19DA7C9C74B1960B85EDC0F7D4D2EC86442E9F315561A514699F215` |
| `R12/benchmark-results/R12-candidate.md` | 16,827 | `2DEE25D774D13DA08DCA95D7E9166418940BEBC08CA151FC149A208876A83AD6` |
| `R12/benchmark-results/R12-candidate.tsv` | 116,734,107 | `C49C94C9C298CFEAFAEB87095F2B8EF9C7513FEB22E9B5BC37F7BE72FF627866` |
| `R12/benchmark-results/R12-worker-strict-source/R12-worker-strict-source.json` | 86,482 | `F0AF4F8EEC861F05365B489614A88D681F4212DE9D17C19EE3752AEE2046CE23` |
| `R12/benchmark-results/R12-worker-strict-source/R12-worker-strict-source.md` | 5,616 | `ED009A6C25E92D21899197FE37AFA939E643D47CEAA92DB449A2950F68945DAD` |

The ten material files total 233,918,240 bytes. The repeated R11 JSON and
Markdown hashes are intentional: the worker strict-source copies are
byte-for-byte identical to the candidate metadata. C0002 remains the current
checkpoint, and this retirement does not create, authorize, or activate a
successor wave.
