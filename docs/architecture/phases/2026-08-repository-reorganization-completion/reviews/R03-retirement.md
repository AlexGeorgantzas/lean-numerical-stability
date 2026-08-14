# R03 retirement and artifact archive

This primary-human review records the terminal retirement boundary for
B0005/R03. The accepted C0003 code checkpoint is
`e20de2f931caa12221e708c341e9cb4f64d29b25`; its acceptance-control commit is
`3ea3efc914b0243673c316f11eda3cba576bebad`. The first acceptance-control CI
run
[31833161196](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31833161196)
(build job
[94873410021](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31833161196/job/94873410021))
correctly rejected a clean-clone portability defect in the new completion
checker: the locally audited expected-postimage tree was an unattached Git
object and therefore was not present after a fresh checkout. The run failed in
the architecture step from `2026-08-14T19:25:57Z` through
`2026-08-14T19:26:05Z`; its Lean build was not run, and no retirement action
was taken.

Checker-only descendant
`a61438448beb02773ef6b0f4f50cbedf8d675d29` reconstructs that tree from the
reachable R03 merge and the committed, hash-checked R0005 patch in a disposable
Git index, then requires the same exact audited tree
`11b2a268de2a65d87da5d2681e2482e87e989494`. A fresh `git clone --no-local`
test proved the tree absent before validation and reconstructed afterward.
That exact final acceptance-control chain head passed GitHub Lean CI run
[31833811860](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31833811860),
build job
[94875463331](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31833811860/job/94875463331),
before retirement. The run and job both concluded `success`; the job ran from
`2026-08-14T19:33:47Z` through `2026-08-14T19:42:15Z`. Its architecture and
source-graph step passed from `19:34:17Z` through `19:38:09Z`, and its library
and smoke-test build passed from `19:38:09Z` through `19:42:12Z`.

The immutable R03 delivery
`1f8ff4ca5b0b136901a2f47d43e1064dc09aa556` remains an ancestor of accepted
C0003 through true merge `0ee06b61ca1c12e8f9492d79b85d1a515c652f09`.
B0005 was retired by `primary-human` at `2026-08-14T19:44:43Z` against
ancestry checkpoint C0003. Its immutable delivery, integration, request, and
projection evidence remain unchanged.

## Remote ref and worktree

The remote delivery ref was deleted using an exact expected-tip lease and was
then verified absent:

| Branch | Remote ref | Expected immutable tip | Post-delete result |
| --- | --- | --- | --- |
| B0005/R03 | `refs/heads/codex/reorg-completion-2026-08-r03-floating-point-foundations-ch01-ch12` | `1f8ff4ca5b0b136901a2f47d43e1064dc09aa556` | absent from `git ls-remote --heads origin` |

Before cleanup, the registered worktree at
`C:\Users\qed_s\higham-worktrees\completion-r03-codex` had exact HEAD
`1f8ff4ca5b0b136901a2f47d43e1064dc09aa556`, its exact B0005 branch checked
out, and empty tracked, staged, unstaged, and ordinary untracked status. Its
seven material ignored artifacts were archived and hash-verified first. The
worktree was then removed with `git worktree remove` without `--force`, and
its registration is absent.

After Git removed the registration and all tracked and material-evidence
content, Windows left only the disposable `.lake` cache at the named path.
That exact single-entry residue was verified and recoverably relocated to
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0003-R03-20260814\disposable-worktree-residue\completion-r03-codex`.
The original named worktree path is absent. The cache residue is not checkpoint
evidence and is excluded from the material-evidence manifest below. The local
delivery branch remains preserved at the exact immutable delivery tip, so the
remote ref can be restored if required.

## Archived ignored evidence

The archive root is
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0003-R03-20260814`.
All paths below are relative to that root. Byte counts and SHA-256 values were
recomputed from the archived files after copying and before worktree removal.

| Relative path | Bytes | SHA-256 |
| --- | ---: | --- |
| `R03/benchmark-results/R03-candidate.json` | 102,836 | `D974CA28F0D656CDD8EBF557A744154BBA17F0745DE30ED731C0A38FB304D844` |
| `R03/benchmark-results/R03-candidate.md` | 23,843 | `5CD3280688009EB59A7735277C5E5BA51072AACAA3B6569D139F2488D916025B` |
| `R03/benchmark-results/R03-candidate.tsv` | 117,090,975 | `98199873425E068D3B74F8595A6CFB9AFE5532974186FD760DFD122B0D273626` |
| `R03/benchmark-results/R03-strict-source/source.json` | 89,841 | `9AA7E7B1A4A4038BE9D047BB643FC63C6A576F2094B6CC5BD053DBE26B3F4EBC` |
| `R03/benchmark-results/R03-strict-source/source.md` | 12,643 | `EB896645791BB20342A9C7CFBD80364F484F9BB5FEC74F8F5643F9235B1B4272` |
| `R03/benchmark-results/R03-tier-audit/audit.json` | 89,837 | `785DF87164CD05DA57A17E20CA0E740176501936DFD27A380ECA06DD0898EB07` |
| `R03/benchmark-results/R03-tier-audit/audit.md` | 12,643 | `9A556D39C0D660C6B8B483766BAC9D36375144CECB34BB2522B56E4D08D640D8` |

The seven material files total 117,422,618 bytes. The archived candidate TSV
is byte-identical to the raw dependency evidence pinned by C0003. C0003
remains the current checkpoint; this retirement does not create, authorize,
plan, or activate a successor wave.
