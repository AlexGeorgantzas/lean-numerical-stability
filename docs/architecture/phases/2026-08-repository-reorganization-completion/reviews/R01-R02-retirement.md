# R01/R02 retirement and artifact archive

This primary-human review records the retirement boundary for B0001/R01 and
B0002/R02. The accepted C0001 code checkpoint is
`117aa2bb7e61f41e1531a78452f9f7f6cd5b0771`; its acceptance-control commit is
`93883eb0ec69a01704ff24ac71713a03f0be5a49`. That exact acceptance-control
commit passed GitHub Lean CI run
[31542177523](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31542177523),
build job
[93946871439](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31542177523/job/93946871439),
before retirement. The run and job both concluded `success`; the job completed
at `2026-08-11T22:30:26Z`.

Both deliveries remain ancestors of the accepted C0001 code checkpoint through
their separate true merges: R01 delivery
`0bdf03a383377c8c6da89d85393e56fca8c00ccd` through merge
`b5966cdc88d136936e6566010cd4113b81f20711`, and R02 delivery
`f790c8413412177bb74f47fee74bb12c48c11155` through merge
`52632d28f0c78438d883bde337700f330895159a`. B0001 and B0002 were retired
together by `primary-human` at `2026-08-11T22:34:24Z` against ancestry
checkpoint C0001. Their integration records remain unchanged.

## Remote refs and worktrees

The two remote delivery refs were deleted using exact expected-tip leases:

| Branch | Remote ref | Expected immutable tip | Post-delete result |
| --- | --- | --- | --- |
| B0001/R01 | `refs/heads/codex/reorg-completion-2026-08-r01-stationary-semiconvergence` | `0bdf03a383377c8c6da89d85393e56fca8c00ccd` | absent from `git ls-remote --heads origin` |
| B0002/R02 | `refs/heads/codex/reorg-completion-2026-08-r02-norm-estimation-ch15` | `f790c8413412177bb74f47fee74bb12c48c11155` | absent from `git ls-remote --heads origin` |

Before cleanup, the named worker worktrees had empty tracked status and exact
HEADs equal to their immutable delivery tips. Ignored delivery evidence was
archived and hash-verified first; only then were ignored caches and evidence
removed and both worktrees removed without force:

| Wave | Removed worktree | Verified pre-removal HEAD |
| --- | --- | --- |
| R01 | `C:\Users\qed_s\higham-worktrees\completion-r01-codex` | `0bdf03a383377c8c6da89d85393e56fca8c00ccd` |
| R02 | `C:\Users\qed_s\higham-worktrees\completion-r02-claude` | `f790c8413412177bb74f47fee74bb12c48c11155` |

The local branch refs remain preserved at those exact immutable tips.

The disposable request-replay worktrees
`C:\Users\qed_s\higham-worktrees\completion-replay-r0001` and
`C:\Users\qed_s\higham-worktrees\completion-replay-r0002` were also verified
clean and detached at exact C0000
`b1b18772d80185ec08f49c818919558645c330a1`. Both were removed without force
after archive verification.

## Archived ignored evidence

The archive root is
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0001-R01-R02-20260811`.
All paths below are relative to that root. Byte counts and SHA-256 values were
recomputed from the archived files after copying and before worktree removal.

| Relative path | Bytes | SHA-256 |
| --- | ---: | --- |
| `R01/benchmark-results/R01-candidate.json` | 101759 | `0A552B738B2F0BF88F52818685A519B420627DD4C78B5B2E46317A5FEEF71E73` |
| `R01/benchmark-results/R01-candidate.md` | 19131 | `6C2FE69D6B6B182FBF9F956E7F27347C038EFC50568041D0961A2FEA437B1519` |
| `R01/benchmark-results/R01-candidate.tsv` | 116692639 | `D2A80F17356569426B23D8B0563D209F4B9D59EC2ACC32A37CD640B4410B8735` |
| `R01/benchmark-results/R01-worker-strict-source/R01-worker-strict-source.json` | 88954 | `68F6BFF1E50C9B4A4BE02A9B2DDF262F8A0706C30B30ED99F4352D5FC74C1705` |
| `R01/benchmark-results/R01-worker-strict-source/R01-worker-strict-source.md` | 8107 | `7766D5B5F0F6EDE1FB2F6C3CF794A53B87691764FD1FBC7746C3D1E8DD8C2204` |
| `R02/benchmark-results/R02-candidate.json` | 100472 | `F2BA6DE16D3346661E93D74A9F1B9EC4A01A2A95334FA4F424AFD2BEF0F615FD` |
| `R02/benchmark-results/R02-candidate.md` | 19148 | `4C2D203055BCEC3CB5F80503B9657CF8147A2CD43978BF43DFFE04B53302442C` |
| `R02/benchmark-results/R02-candidate.tsv` | 116722355 | `308C48787CE3FBF69360841F2487570FB4B721939079CE90D939E8EAD75873CF` |
| `R02/benchmark-results/R02-strict-source/source.json` | 100472 | `F2BA6DE16D3346661E93D74A9F1B9EC4A01A2A95334FA4F424AFD2BEF0F615FD` |
| `R02/benchmark-results/R02-strict-source/source.md` | 19148 | `4C2D203055BCEC3CB5F80503B9657CF8147A2CD43978BF43DFFE04B53302442C` |
| `R02/docs/architecture/deliveries/R02/postimage/check_layout_postimage.log` | 250 | `B9CA9C11434414ECDC50730D1B79A37C0C34C6A35DFEE87D6AFB3D61F7032B7B` |

The repeated R02 JSON and Markdown hashes are intentional: the delivery's
strict-source copies are byte-for-byte identical to its candidate metadata.
