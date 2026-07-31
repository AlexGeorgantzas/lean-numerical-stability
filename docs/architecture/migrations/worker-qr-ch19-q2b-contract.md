# QR / Chapter 19 Q2B contract refresh

This is the Q2B contract/evidence record for the worker resumed from the live
integrator checkpoint.  It does not replace the frozen packet artifacts.

## Identity

| Item | Value |
| --- | --- |
| Packet semantic base | `6487fc33088523b8f27ecde9ad613515b78f9977` |
| Live starting checkpoint | `48242807d4149210926eccf90a326d287fc0860c` (`origin/main`) |
| Worker branch | `codex/org-qr-ch19` |
| Repository | `https://github.com/AlexGeorgantzas/lean-numerical-stability.git` |
| Lean toolchain | `leanprover/lean4:v4.29.0-rc3` |
| Mathlib revision | `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b` |
| Contract source snapshot | integrated owner snapshot `420e4f93e2a5d31b2bf5b73740ca4146de7b0921` |

The packet baseline and all route/ownership artifacts remain immutable.  The
420 snapshot is used only because the inherited QR contract pins its source
and `.ilean` hashes to that published integration snapshot; the worker code
starts at live `origin/main@48242807`.  Every 420 owner source hash was checked
against `qr-ch19-frozen-owners.tsv` before this refresh.  The exact frozen
source witness is external at
`evidence/frozen-source-420-flat/` and the exact compiled witness is external
at `evidence/frozen-ilean-420-flat/`; both contain 59 owner files and all 59
hashes match the frozen owner table.

## Frozen contract

The format-2 packet stream is retained at
`evidence/baseline/phase12b-recursive-declarations-v2.tsv`, SHA-256
`32ADA469E27A971E9B0BB972F29C51E1DCBE99104A1492D4C69549C339825563`, with
3991 QR declarations.  The reviewed contract records 59 historical owners,
3331 command groups, 60 destinations, 22 inherited private rewrites after
Householder + Q2A, and a destination DAG with 374 typed destination edges
(163 signature and 211 body/proof) across 12159 declaration-edge instances.
The frozen source-import graph has 184 rows.  The two source aliases in
`Higham19Theorem6ActualSource` remain explicit route rows.

The Q2B checker refresh adds two reviewed invariants: imports from any moved
historical Chapter 19 owner resolve to that owner's canonical source leaf, and
the late `Higham19WYApplicationClosure` leaf preserves
`NumStability.Algorithms.LU.BlockLUFirstOrderFamilies` while its QR dependency
resolves to canonical `GramSchmidtPolar`.  The checker negative self-tests
cover both mappings, exact wrappers, and typed-edge drift.

## Wave order

The remaining source owners are scheduled by the direct source-import graph
and the frozen declaration DAG.  The four cross-lane owners stay separate;
`Higham19Alg12MGSSourceRate` and `Higham19Theorem5SourceClosure` must precede
their own same-lane dependents, so those two tail commits are placed at the
first dependency-safe late points.  `Higham19WYApplicationClosure` is a
separate late handoff after BlockLU/Chapter 13 integration.  Each tail remains
one owner, one canonical leaf, one exact wrapper, and its own isolated tests.

No LSQ, Chapter 20, BlockLU, Chapter 13, global aggregate, root-test,
manifest, toolchain, CI, or other shared path is edited by this worker.

## Evidence locations

The pristine path-oriented source snapshot is external at
`/home/mymel/lean/reorg/codex-qr-ch19/evidence/frozen-source-420`; the checker
view is the flattened
`/home/mymel/lean/reorg/codex-qr-ch19/evidence/frozen-source-420-flat`.
The exact compiled owner `.ilean` snapshot is the flattened
`/home/mymel/lean/reorg/codex-qr-ch19/evidence/frozen-ilean-420-flat`; its
locked witness command was `bash scripts/with_lean_lock.sh lake build
NumStability` in the detached 420 worktree, followed by explicit owner-file
hash validation (`owners=59 matches=59 mismatches=0`).  Candidate format-2
streams and build logs remain under the external `evidence/` directory and
are named in the delivery report.

The live-base equivalent scope gate uses `evidence/LIVE_BASE_SHA.txt` rather
than the packet's stale `BASE_SHA.txt`; it passed with base
`48242807d4149210926eccf90a326d287fc0860c`, 42 touched paths, and no forbidden
or unallowlisted paths.  The checker pre gate passed with 59 owners, 3991
declarations, 3331 command groups, and the exact 22 inherited private-rewrite
rows from live main.
